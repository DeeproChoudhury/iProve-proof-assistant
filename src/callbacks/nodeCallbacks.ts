import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { conjunct, isBlockEnd, isBlockStart, isTerm } from "../util/trees";
import Z3Solver from "../logic/Solver";
import { AnyNodeType, InductionNodeType, ProofNodeType, StatementNodeData, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { getInputs, getOutputs, invalidateReasonForNode, isStatementNode, setNodeWithId, setStatementsForNode, shiftReasonsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { unwrap_statements, updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";
import { LI, LogicInterface, ProofOutcome } from "../logic/LogicInterface";
import { Line, Term, TypeDef } from "../types/AST";
import { IProveError } from "../types/ErrorLocation";
import { parse_error } from "../util/errors";
import { checkReason, z3Reason } from "../util/reasons";
import { makeSharedNodeCallbacks } from "./sharedNodeCallbacks";

export type NodeCallbacks = StatementNodeData["thisNode"];

export const makeNodeCallbacks = (
  nodesRef: MutableRefObject<AnyNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  setNodes: Setter<AnyNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<IProveError | undefined>,
  setStopGlobalCheck: Setter<boolean | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
): NodeCallbacks => {
  const setNode = setNodeWithId(setNodes, isStatementNode, nodeId);

  const shiftReasons = shiftReasonsForNode(setNode);
  const invalidateReason = invalidateReasonForNode(setNode);

  const givens = makeStatementListCallbacks(setStatementsForNode(setNode, "givens"), setError);
  const proofSteps = makeStatementListCallbacks(setStatementsForNode(setNode, "proofSteps"), setError);
  const goals = makeStatementListCallbacks(setStatementsForNode(setNode, "goals"), setError);
  const statementLists = {
      givens: {
        ...givens,
        add: (index?: number) => {
          shiftReasons("givens", index, 1);
          givens.add(index);
        },
        update: (index: number, statementValue: string) => {
          invalidateReason("givens", index);
          givens.update(index, statementValue);
        },
        remove: (index: number) => {
          invalidateReason("givens", index);
          shiftReasons("givens", index, -1);
          givens.remove(index);
        },
      },
      proofSteps: {
        ...proofSteps,
        add: (index?: number) => {
          shiftReasons("proofSteps", index, 1);
          proofSteps.add(index);
        },
        update: (index: number, statementValue: string) => {
          invalidateReason("proofSteps", index);
          proofSteps.update(index, statementValue);
        },
        remove: (index: number) => {
          invalidateReason("proofSteps", index);
          shiftReasons("proofSteps", index, -1);
          proofSteps.remove(index);
        },
        removeReason: (index: number) => {
          invalidateReason("proofSteps", index);
          proofSteps.removeReason(index);
        }
      },
      goals: {
        ...goals,
        add: (index?: number) => {
          shiftReasons("goals", index, 1);
          goals.add(index);
        },
        update: (index: number, statementValue: string) => {
          invalidateReason("goals", index);
          goals.update(index, statementValue);
        },
        remove: (index: number) => {
          invalidateReason("goals", index);
          shiftReasons("proofSteps", index, -1);
          goals.remove(index);
        },
        removeReason: (index: number) => {
          invalidateReason("goals", index);
          goals.removeReason(index);
        }
      }
    };
  return {
    ...makeSharedNodeCallbacks(setNodes, isStatementNode, nodeId),
    ...statementLists,
    parseAll: () => {
      setError(undefined);
      statementLists.givens.parseAll();
      statementLists.proofSteps.parseAll();
      statementLists.goals.parseAll();
      setNode(node => {
        return {
          ...node,
          data: {
            ...node.data, 
            allParsed: [
              node.data.givens,
              node.data.proofSteps,
              node.data.goals,
            ].every(list => list.every(statement => statement.parsed))
          }
        }    
      });
    },
    checkInternal: async () => {
        // const node = nodesRef.current.find(n => n.id === nodeId);
        // if (!node || node.type !== "proofNode") return;
        // for (const listField of ["proofSteps", "goals"] as const) {
        //   for (let i = 0; i < node.data[listField].length; i++) {
        //     await checkReason(node.data, node.data[listField][i], status => node.data.thisNode[listField].updateReasonStatus(i, status), (_result) => {});
        //   }
        // }
    },
    recheckReasons: async () => {
      const node = nodesRef.current.find(n => n.id === nodeId);
      if (!node || node.type !== "proofNode") return;
      for (const listField of ["proofSteps", "goals"] as const) {
        for (let i = 0; i < node.data[listField].length; i++) {
          const reason = node.data[listField][i].reason;
          if (reason && ["unchecked", "invalid"].includes(reason.status))
            await checkReason(node.data, node.data[listField][i], status => node.data.thisNode[listField].updateReasonStatus(i, status), (_result) => {});
        }
      }
    },
    autoAddReasons: () => {
      const autoAddReason = (statement: StatementType, index: number): StatementType => {
        if (
            (statement.parsed && !isTerm(statement.parsed))
            || statement.reason?.status === "valid"
            || statement.reason?.status === "checking"
          ) return statement;
        return { ...statement, reason: z3Reason([...new Array(index).keys()]) }
      };
      setNode(node => {
        if (node.type !== "proofNode") return node;
        return {
          ...node,
          data: {
            ...node.data,
            proofSteps: node.data.proofSteps.map((s, i) => autoAddReason(s, i + node.data.givens.length)),
            goals: node.data.goals.map((s, i) => autoAddReason(s, i + node.data.givens.length + node.data.proofSteps.length))
          }
        }    
      });
    },
    checkEdges: async () => {
      // here we should get all incoming edges & nodes to nodeID
      // use the proofSteps (maybe goals?) of the incoming nodes and the givens of nodeId
      // to deduce whether the implication holds (using z3)
      // if yes, mark all edges + nodeId as true
      // TODO: Fix this
      const currEdges = edgesRef.current;
      const currNodes = nodesRef.current;
      const node = currNodes.find((n) => n.id === nodeId);
      if (!node || !isStatementNode(node)) return;
      
      const incomingEdges = currEdges.filter((e) => e.target === nodeId);
      // get all nodes that have incoming edge to nodeId
      // should probably use getIncomers from reactflow
      const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
      const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
      const givens = incomingNodes.flatMap(getOutputs);
      const expImplications = getInputs(node);
      
      if (expImplications.some(s => !s.parsed)) {
        return; // TODO: show error message here
      }
      
      // check that exp_implications follows from givens with z3
      {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}
      let success: boolean = false;

      let goal: Term | undefined = conjunct(unwrap_statements(expImplications))
      if (goal) { 
        const verdict = await LI.entails(unwrap_statements(givens), goal)
        success = (verdict.kind == "Valid")
        
        if (verdict.kind == "Error") {
          setError(parse_error(verdict))
        }
        else if (verdict.kind != "Valid") {
          setError({ kind: "Proof" })
        }
      } else {
        setError({ kind: "Semantic", msg: "Malformed givens (they may not be declarations or definitions!)" })
      }
      
      {/* END LOGIC INTERFACE CRITICAL REGION */}

      setNode((node) => {
        //set nodes
        return {
          ...node,
          data: {
            ...node.data,
            edgesStatus: success ? "valid" : "invalid"
          }
        };
      });
      setEdges(eds => {
        //set edges
        return eds.map((edge) => {
          if (edge.target === nodeId) {
            edge.type = success ? "checked" : "invalid";
          }
          return edge;
        });
      });
    },
    setWrappers: () => {
      // sets the indentation level for each statement inside a node
      // this is run whenever the user leaves the input field of a statement and sees if 
      // any indentations can be updated (only goes through proofSteps since no indentations 
      // should be possible in givens and goals
      setNode((n) => {
        const wrappers = [];
        const proofSteps = [];
        for (const oldStep of n.data.proofSteps) {
          if (!oldStep.parsed) {
            proofSteps.push(oldStep);
            continue;
          }
          if (isBlockStart(oldStep.parsed)) {
            // new scope so I want first line to not be wrapped in itself
            proofSteps.push({
              ...oldStep,
              wrappers: [...wrappers]
            })
            wrappers.push(oldStep.parsed);
            continue;
          } else if (isBlockEnd(oldStep.parsed)) {
            wrappers.pop();
          }
          proofSteps.push({
            ...oldStep,
            wrappers: [...wrappers]
          })
        }
        //set nodes
        return {
          ...n,
          data: {
            ...n.data,
            proofSteps
          }
        };
      });
    }
  };
};
