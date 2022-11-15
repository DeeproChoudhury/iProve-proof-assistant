import { MutableRefObject } from "react";
import { Edge, Node } from "reactflow";
import { ASTSMTLIB2 } from "../parser/AST";
import Z3Solver from "../solver/Solver";
import { ErrorLocation } from "../types/ErrorLocation";
import { InductionData, NodeData } from "../types/Node";
import { StatementKind, StatementType } from "../types/Statement";
import { getResults, listField, setInductionNodeWithId, setInductionStatementsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";


export const makeInductionNodeCallbacks = (
  inductionNodesRef: MutableRefObject<Node<InductionData>[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setInductionNodes: Setter<Node<InductionData>[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
) => {
  const setNode = setInductionNodeWithId(setInductionNodes, nodeId);
  const statementLists = {
    types: makeStatementListCallbacks(setInductionStatementsForNode(setNode, "type")),
    predicate: makeStatementListCallbacks(setInductionStatementsForNode(setNode, "predicate")),
    baseCases: makeStatementListCallbacks(setInductionStatementsForNode(setNode, "baseCase")),
    inductiveCase: makeStatementListCallbacks(setInductionStatementsForNode(setNode, "inductiveCase")),
    inductiveHypotheses: makeStatementListCallbacks(setInductionStatementsForNode(setNode, "inductiveHypothesis")),
  };
  return {
    delete: (): void => setInductionNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    ...statementLists,
    statementList: (k: StatementKind) => statementLists[listField(k) as keyof typeof statementLists],
    checkSyntax: (): void => setNode(node => {
      setError(undefined);

      return {
        ...node,
        data: {
          ...node.data,
          types: node.data.types.map(updateWithParsed(setError)),
          predicate: node.data.predicate.map(updateWithParsed(setError)),
          baseCases: node.data.baseCases.map(updateWithParsed(setError)),
          inductiveCase: node.data.inductiveCase.map(updateWithParsed(setError)),
          inductiveHypotheses: node.data.inductiveHypotheses.map(updateWithParsed(setError)),
        }
      };
    }),
  };
};

export type InductionNodeCallbacks = ReturnType<ReturnType<typeof makeInductionNodeCallbacks>>;