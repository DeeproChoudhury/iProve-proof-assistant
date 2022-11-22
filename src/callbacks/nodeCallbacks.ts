import { MutableRefObject } from "react";
import { Edge, Node } from "reactflow";
import { ASTSMTLIB2, isBlockEnd, isBlockStart, isTerm } from "../parser/AST";
import Z3Solver from "../solver/Solver";
import { ErrorLocation } from "../types/ErrorLocation";
import { ListField, StatementNodeData, StatementNodeType } from "../types/Node";
import { CheckStatus } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { getResults, invalidateReasonForNode, setNodeWithId, setStatementsForNode, shiftReasonsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { statementToZ3, updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks, StatementListCallbacks } from "./statementListCallbacks";


export const makeNodeCallbacks = (
  nodesRef: MutableRefObject<StatementNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
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
    checkSyntax: () => setNode(node => {
      setError(undefined);
      return {
        ...node,
        data: {
          ...node.data,
          givens: node.data.givens.map(updateWithParsed(setError)),
          proofSteps: node.data.proofSteps.map(updateWithParsed(setError)),
          goals: node.data.goals.map(updateWithParsed(setError))
        }
      };
    }),
    checkInternalAssertions: async () => {
      const localZ3Solver = new Z3Solver.Z3Prover("");
      const node = nodesRef.current.find((n) => n.id === nodeId);
      if (!node || node.type !== "proofNode") { 
        /* only need to check internal assertions for proof nodes */
        return;
      }
      let reasons = node.data.givens;
      let goals = node.data.proofSteps.concat(node.data.goals);
      const declarations = node.data.declarationsRef.current.map(declaration => {
        return statementToZ3(declaration);
      }).join("\n");
      let smtReasons = reasons.map(reason => {
        const reasonStr = statementToZ3(reason);
        if (!reason.parsed) return "";
        if (isTerm(reason.parsed)) return `(assert ${reasonStr})`;
        else return reasonStr;
      }).join("\n");
      
      const shouldProve = (s: StatementType) => {
        if (!s.parsed) {
          return false;
        }
        const parsed = s.parsed;
        return !(parsed.kind === "VariableDeclaration" || 
          parsed.kind === "EndScope" || 
          parsed.kind == "BeginScope" || 
          parsed.kind == "FunctionDeclaration" || 
          parsed.kind == "Assumption"); 
      }

      for (const goal of goals) {
        if (!goal.parsed || !shouldProve(goal)) {
          if (!goal.parsed) {
            setStopGlobalCheck(true);
          }
          if (goal.parsed?.kind === "VariableDeclaration" || goal.parsed?.kind === "FunctionDeclaration") {
            smtReasons = smtReasons + `\n ${statementToZ3(goal)}\n`;
          }
          return;
        }
        const goalStr = statementToZ3(goal);
        const smtConclusion = "(assert (not " + goalStr + "))";
        const output = await localZ3Solver.solve(declarations + "\n" + smtReasons + "\n" + smtConclusion + "\n (check-sat)")
        if (output === "unsat\n") {
          // check passed so can add goal to reasons and move on to next goal 
          smtReasons = smtReasons + `\n (assert ${goalStr})\n`;
        } else {
          setStopGlobalCheck(true);
          return;
        }
      }
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
      if (!node) return true;

      const incomingEdges = currEdges.filter((e) => e.target === nodeId);
      // get all nodes that have incoming edge to nodeId
      // should probably use getIncomers from reactflow
      const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
      const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
      const givens = incomingNodes.map(node => getResults(node)).flat();
      const expImplications = node.data.givens;
      
      if (declarationsRef.current.some(s => !s.parsed) || expImplications.some(s => !s.parsed)) {
        return false; // TODO: show error message here
      }
      
      // check that exp_implications follows from givens with z3
      console.log(declarationsRef.current);
      const smtDeclarations = declarationsRef.current.map((declaration: StatementType) => {
        if (!declaration.parsed) return "";
        return ASTSMTLIB2(declaration.parsed);
      }).join("\n");
      const smtReasons = givens.map(given => {
        if (!given.parsed) return "";
        if (given.parsed?.kind === "FunctionDeclaration" || given.parsed?.kind === "VariableDeclaration") {
          return ASTSMTLIB2(given.parsed);
        }
        return `(assert ${ASTSMTLIB2(given.parsed)})`
      }).join("\n");
      console.log(smtDeclarations);
      console.log(smtReasons);
      const smtConclusions = expImplications.map((conclusion: StatementType) => {
        if (!conclusion.parsed) return "";
        return "(assert (not " + ASTSMTLIB2(conclusion.parsed) + "))";
      }).join("\n");
      console.log(smtConclusions);
      const output = await z3.solve(smtDeclarations + "\n" + smtReasons + "\n" + smtConclusions + "\n (check-sat)")
      const success = output === "unsat\n";
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
