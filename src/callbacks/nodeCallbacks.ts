import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { conjunct, isBlockEnd, isBlockStart } from "../util/trees";
import Z3Solver from "../solver/Solver";
import { ErrorLocation } from "../types/ErrorLocation";
import { InductionNodeType, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { invalidateReasonForNode, setNodeWithId, setStatementsForNode, shiftReasonsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { statementToZ3, updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";
import { LogicInterface } from "../logic/LogicInterface";
import { Term } from "../types/AST";



export const makeNodeCallbacks = (
  nodesRef: MutableRefObject<StatementNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  inductionNodesRef: MutableRefObject<InductionNodeType[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setNodes: Setter<StatementNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
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
      givens,
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
      const LI = new LogicInterface;

      // Add globals/givens to the LogicInterface state
      node.data.declarationsRef.current.forEach(
        (declaration: StatementType) => statementToZ3(declaration, LI, "global")
      );
      reasons.forEach(
        (reason: StatementType) => statementToZ3(reason, LI, "given")
      );

      // Iterate over each node goal, setting it as the goal in LogicInterface
      // before rendering as SMT and sending to Z3
      goals.forEach(
        async (goal: StatementType) => {
          if (statementToZ3(goal, LI, "goal")) {
            const output = await localZ3Solver.solve(`${LI}`)
            if (output === "unsat\n") {
              statementToZ3(goal, LI, "goal")
              return
            }
          }
          setStopGlobalCheck(true);
        })
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
      console.log(declarationsRef.current);

      {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}
      const LI = new LogicInterface;

      // Add globals/givens to the LogicInterface state
      declarationsRef.current.forEach(
        (declaration: StatementType) => statementToZ3(declaration, LI, "global")
      );
      givens.forEach(
        (reason: StatementType) => statementToZ3(reason, LI, "global")
      );

      // Iterate over each node goal, setting it as the goal in LogicInterface
      // before rendering as SMT and sending to Z3
      let goal: Term | undefined = conjunct(
        expImplications
          .map(v => v.parsed)
          .filter(v => v != undefined)
          .map(v => v as Term)
      );

      let success: boolean = true;
      if (goal) {
        LI.setGoal(goal)
        const output = await z3.solve(`${LI}`)
        success = output === "unsat\n"
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
