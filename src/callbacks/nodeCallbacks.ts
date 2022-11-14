import { MutableRefObject } from "react";
import { Edge, Node } from "reactflow";
import { ASTSMTLIB2 } from "../parser/AST";
import Z3Solver from "../solver/Solver";
import { ErrorLocation } from "../types/ErrorLocation";
import { NodeData } from "../types/Node";
import { StatementKind, StatementType } from "../types/Statement";
import { getResults, invalidateReasonForNode, listField, setNodeWithId, setStatementsForNode, shiftReasonsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks, StatementListCallbacks } from "./statementListCallbacks";


export const makeNodeCallbacks = (
  nodesRef: MutableRefObject<Node<NodeData>[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setNodes: Setter<Node<NodeData>[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
) => {
  const setNode = setNodeWithId(setNodes, nodeId);

  const shiftReasons = shiftReasonsForNode(setNode);
  const invalidateReason = invalidateReasonForNode(setNode);

  const givens = makeStatementListCallbacks(setStatementsForNode(setNode, "given"));
  const proofSteps = makeStatementListCallbacks(setStatementsForNode(setNode, "proofStep"));
  const goals = makeStatementListCallbacks(setStatementsForNode(setNode, "goal"));
  const statementLists = {
      givens,
      proofSteps: {
        add: (index?: number) => {
          shiftReasons("proofStep", index, 1);
          proofSteps.add(index);
        },
        update: (index: number, statementValue: string) => {
          invalidateReason("proofStep", index);
          proofSteps.update(index, statementValue);
        },
        remove: (index: number) => {
          invalidateReason("proofStep", index);
          shiftReasons("proofStep", index, -1);
          proofSteps.remove(index);
        },
        addReason: proofSteps.addReason,
        removeReason: (index: number) => {
          invalidateReason("proofStep", index);
          proofSteps.removeReason(index);
        }
      },
      goals: {
        add: (index?: number) => {
          shiftReasons("goal", index, 1);
          goals.add(index);
        },
        update: (index: number, statementValue: string) => {
          invalidateReason("goal", index);
          goals.update(index, statementValue);
        },
        remove: (index: number) => {
          invalidateReason("goal", index);
          shiftReasons("proofStep", index, -1);
          goals.remove(index);
        },
        addReason: goals.addReason,
        removeReason: (index: number) => {
          invalidateReason("goal", index);
          goals.removeReason(index);
        }
      }
    };
  return {
    delete: (): void => setNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    ...statementLists,
    statementList: (k: StatementKind): StatementListCallbacks => statementLists[listField(k)],
    checkSyntax: (): void => setNode(node => {
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
    checkEdges: () => {
      // here we should get all incoming edges & nodes to nodeID
      // use the proofSteps (maybe goals?) of the incoming nodes and the givens of nodeId
      // to deduce whether the implication holds (using z3)
      // if yes, set correctImplication = true and mark all edges + nodeId as true
      let correctImplication = false;
      // TODO: Fix this
      const currEdges = edgesRef.current;
      const currNodes = nodesRef.current;
      const node = currNodes.find((n) => n.id === nodeId);
      if (!node) return;

      const incomingEdges = currEdges.filter((e) => e.target === nodeId);
      // get all nodes that have incoming edge to nodeId
      // should probably use getIncomers from reactflow
      const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
      const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
      const givens = incomingNodes.map(node => getResults(node)).flat();
      const exp_implications = node?.data.givens;
      
      // check that exp_implications follows from givens with z3
      correctImplication = false;
      console.log(declarationsRef.current);
      const smtDeclarations = declarationsRef.current.map((declaration: StatementType) => {
        return ASTSMTLIB2(declaration.parsed);
      }).join("\n");
      const smtReasons = givens.map(given => {
        if (given.parsed?.kind === "FunctionDeclaration" || given.parsed?.kind === "VariableDeclaration") {
          return ASTSMTLIB2(given.parsed);
        }
        return `(assert ${ASTSMTLIB2(given.parsed)})`
      }).join("\n");
      console.log(smtDeclarations);
      console.log(smtReasons);
      const smtConclusions = exp_implications.map((conclusion: StatementType) => {
        return "(assert (not " + ASTSMTLIB2(conclusion?.parsed) + "))";
      }).join("\n");
      console.log(smtConclusions);
      z3.solve(smtDeclarations + "\n" + smtReasons + "\n" + smtConclusions + "\n (check-sat)").then((output: string) => {
        if (output === "unsat\n") {
          correctImplication = true;
        } else {
          correctImplication = false;
        }
        setNodeWithId(setNodes, nodeId)((node) => {
          //set nodes
          return {
            ...node,
            data: {
              ...node.data,
              correctImplication
            }
          };
        });
        setEdges(eds => {
          //set edges
          return eds.map((edge) => {
            if (edge.target === nodeId) {
              edge.type = correctImplication ? "checked" : "invalid";
            }
            return edge;
          });
        });
      })
    }
  };
};

export type NodeCallbacks = ReturnType<ReturnType<typeof makeNodeCallbacks>>;
