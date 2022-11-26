import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import Z3Solver from "../solver/Solver";
import { ErrorLocation } from "../types/ErrorLocation";
import { InductionNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { setNodeWithId, setStatementsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";


export const makeInductionNodeCallbacks = (
  inductionNodesRef: MutableRefObject<InductionNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setInductionNodes: Setter<InductionNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
) => {
  const setNode = setNodeWithId(setInductionNodes, nodeId);
  return {
    delete: (): void => setInductionNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    types: makeStatementListCallbacks(setStatementsForNode(setNode, "types")),
    predicate: makeStatementListCallbacks(setStatementsForNode(setNode, "predicate")),
    baseCases: makeStatementListCallbacks(setStatementsForNode(setNode, "baseCases")),
    inductiveCases: makeStatementListCallbacks(setStatementsForNode(setNode, "inductiveCases")),
    inductiveHypotheses: makeStatementListCallbacks(setStatementsForNode(setNode, "inductiveHypotheses")),
    checkSyntax: (): void => setNode(node => {
      setError(undefined);

      return {
        ...node,
        data: {
          ...node.data,
          types: node.data.types.map(updateWithParsed(setError)),
          predicate: node.data.predicate.map(updateWithParsed(setError)),
          baseCases: node.data.baseCases.map(updateWithParsed(setError)),
          inductiveCase: node.data.inductiveCases.map(updateWithParsed(setError)),
          inductiveHypotheses: node.data.inductiveHypotheses.map(updateWithParsed(setError)),
        }
      };
    }),
  };
};

export type InductionNodeCallbacks = ReturnType<ReturnType<typeof makeInductionNodeCallbacks>>;
