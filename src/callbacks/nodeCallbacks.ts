import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { conjunct, isBlockEnd, isBlockStart } from "../util/trees";
import Z3Solver from "../logic/Solver";
import { InductionNodeType, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { invalidateReasonForNode, setNodeWithId, setStatementsForNode, shiftReasonsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { unwrap_statements, updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";
import { LI, LogicInterface, ProofOutcome } from "../logic/LogicInterface";
import { Line, Term } from "../types/AST";
import { IProveError } from "../types/ErrorLocation";
import { parse_error } from "../util/errors";



export const makeNodeCallbacks = (
  nodesRef: MutableRefObject<StatementNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  inductionNodesRef: MutableRefObject<InductionNodeType[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setNodes: Setter<StatementNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<IProveError | undefined>,
  setStopGlobalCheck: Setter<boolean | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
) => {
  const setNode = setNodeWithId(setNodes, nodeId);

  const shiftReasons = shiftReasonsForNode(setNode);
  const invalidateReason = invalidateReasonForNode(setNode);

  const givens = makeStatementListCallbacks(setStatementsForNode(setNode, "givens"));
  const proofSteps = makeStatementListCallbacks(setStatementsForNode(setNode, "proofSteps"));
  const goals = makeStatementListCallbacks(setStatementsForNode(setNode, "goals"));
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
    delete: (): void => setNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    ...statementLists,
    checkSyntax: () => {
      setNode(node => {return {
        ...node,
        data: {
          ...node.data,
          parsed: undefined
        }
      }})
      setNode(node => {
        setError(undefined);
        const givens = node.data.givens.map(updateWithParsed(setError));
        const proofSteps = node.data.proofSteps.map(updateWithParsed(setError));
        const goals = node.data.goals.map(updateWithParsed(setError));
        const parsed = [...givens, ...proofSteps, ...goals].every((statement) => statement.parsed)
        return {
          ...node,
          data: {
            ...node.data,
            givens: givens,
            proofSteps: proofSteps,
            goals: goals,
            parsed: parsed
          }
        };
      })
    },
    checkInternalAssertions: async () => {
      const localZ3Solver = new Z3Solver.Z3Prover("");
      const node = nodesRef.current.find((n) => n.id === nodeId);
      if (!node || node.type !== "proofNode") { 
        /* only need to check internal assertions for proof nodes */
        return;
      }
      let reasons = node.data.givens;
      let goals = node.data.proofSteps.concat(node.data.goals);

      {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}

      // TODO: WIRE UP TYPES BOX?
      LI.setDeclarations(unwrap_statements(node.data.declarationsRef.current))

      let c_givens: Line[] = unwrap_statements(reasons);
      for (let G of unwrap_statements(goals)) {
        const verdict: ProofOutcome = await LI.entails(c_givens, G)
        if (verdict.kind == "Valid") { c_givens.push(G); continue; }
        else if (verdict.kind == "Error") setError(parse_error(verdict))
        else { setStopGlobalCheck(true); setError({
            kind: "Proof"
          })
        }
      }

      {/* END LOGIC INTERFACE CRITICAL REGION */}
    },
    checkEdges: async () => {
      // here we should get all incoming edges & nodes to nodeID
      // use the proofSteps (maybe goals?) of the incoming nodes and the givens of nodeId
      // to deduce whether the implication holds (using z3)
      // if yes, mark all edges + nodeId as true
      // TODO: Fix this
      const currEdges = edgesRef.current;
      const currNodes = nodesRef.current;
      const currInductionNodes = inductionNodesRef.current;
      const node = currNodes.find((n) => n.id === nodeId);
      if (!node) return true;
      
      const incomingEdges = currEdges.filter((e) => e.target === nodeId);
      console.log(incomingEdges)
      // get all nodes that have incoming edge to nodeId
      // should probably use getIncomers from reactflow
      const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
      const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
      const incomingInductionNodes = currInductionNodes.filter(node => incomingNodesIds.has(node.id));
      const inductionGivens = incomingInductionNodes.map(node => node.data.motive[0]);
      const givens = [...incomingNodes.flatMap(node => node.data.goals), ...inductionGivens];
      const expImplications = node.data.givens;
      
      if (declarationsRef.current.some(s => !s.parsed) || expImplications.some(s => !s.parsed)) {
        return false; // TODO: show error message here
      }
      
      // check that exp_implications follows from givens with z3
      {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}
      let success: boolean = false;

      // TODO: WIRE UP TYPES BOX?
      LI.setDeclarations(unwrap_statements(node.data.declarationsRef.current))

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
            correctImplication: success ? "valid" : "invalid"
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
      return success;
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

export type NodeCallbacks = ReturnType<ReturnType<typeof makeNodeCallbacks>>;
function setCheckFailed(arg0: boolean) {
  throw new Error("Function not implemented.");
}

