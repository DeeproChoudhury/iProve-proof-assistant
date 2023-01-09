import { Edge } from "reactflow";
import type { Draft } from "immer";
import create from "zustand";
import { immer } from "zustand/middleware/immer";
import { IProveError } from "../types/ErrorLocation";
import { AnyNodeType, InductionNodeListField, InductionNodeType, ListField, StatementNodeListField, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { makeAnyNodeActions } from "../actions/anyNode";
import { makeStatementListActions } from "../actions/statementList";
import { makeStatementListWithReasonsActions } from "../actions/statementListWithReasons";
import { makeInductionNodeActions } from "../actions/inductionNode";
import { makeStatementNodeActions } from "../actions/statementNode";
import { makeFlowActions } from "../actions/flow";
import { makeGlobalActions } from "../actions/global";

type State = {
  nodes: AnyNodeType[];
  edges: Edge[];
  declarations: StatementType[];
  typeDeclarations: StatementType[];
  nextNodeId: number;

  error: IProveError | undefined;
}

type Actions = {
  actions: {
    global: ReturnType<typeof makeGlobalActions>,
    flow: ReturnType<typeof makeFlowActions>,
    declarations: ReturnType<typeof makeStatementListActions>
    typeDeclarations: ReturnType<typeof makeStatementListActions>
    forNode: (nodeId: string) => ReturnType<typeof makeAnyNodeActions>,
    forStatementNode: (nodeId: string) =>
      ReturnType<typeof makeAnyNodeActions>
      & Record<StatementNodeListField, ReturnType<typeof makeStatementListWithReasonsActions>>
      & ReturnType<typeof makeStatementNodeActions>
    forInductionNode: (nodeId: string) =>
      ReturnType<typeof makeAnyNodeActions>
      & Record<InductionNodeListField, ReturnType<typeof makeStatementListActions>>
      & ReturnType<typeof makeInductionNodeActions>
  }
}

export type StoreType = State & Actions;

export type IProveDraft = Draft<State & Actions>;

const getNodeOrThrow = (store: StoreType, nodeId: string): AnyNodeType => {
  const node = store.nodes.find(n => n.id === nodeId)
  if (!node) throw new Error("nonexistent node");
  return node;
}

const getStatementNodeOrThrow = (store: StoreType, nodeId: string): StatementNodeType => {
  const node = getNodeOrThrow(store, nodeId);
  if (node.type === "inductionNode") throw new Error("wrong node type");
  return node;
}

const getInductionNodeOrThrow = (store: StoreType, nodeId: string): InductionNodeType => {
  const node = getNodeOrThrow(store, nodeId);
  if (node.type !== "inductionNode") throw new Error("wrong node type");
  return node;
}

const listFieldToStmtNodeStmtListActions = (set: (cb: (draft: IProveDraft) => void) => void, nodeId: string, listField: StatementNodeListField) => makeStatementListWithReasonsActions(set, draft => ({ node: getStatementNodeOrThrow(draft, nodeId), listField }));

const listFieldToInductionNodeStmtListActions = (set: (cb: (draft: IProveDraft) => void) => void, nodeId: string, listField: InductionNodeListField) => makeStatementListActions(set, draft => getInductionNodeOrThrow(draft, nodeId).data[listField]);

export const useIProveStore = create(
  immer<State & Actions>((set) => {
    return {
      nodes: [],
      edges: [],
      nextNodeId: 0,
      error: undefined,
      declarations: [],
      typeDeclarations: [],

      actions: {
        global: makeGlobalActions(set),
        flow: makeFlowActions(set),
        declarations: makeStatementListActions(set, draft => draft.declarations),
        typeDeclarations: makeStatementListActions(set, draft => draft.typeDeclarations),
        forNode: (nodeId: string) => makeAnyNodeActions(set, draft => getNodeOrThrow(draft, nodeId)),
        forStatementNode: (nodeId: string) => ({
          ...makeAnyNodeActions(set, draft => getNodeOrThrow(draft, nodeId)),
          givens: listFieldToStmtNodeStmtListActions(set, nodeId, "givens"),
          proofSteps: listFieldToStmtNodeStmtListActions(set, nodeId, "proofSteps"),
          goals: listFieldToStmtNodeStmtListActions(set, nodeId, "goals"),
          ...makeStatementNodeActions(set, draft => getStatementNodeOrThrow(draft, nodeId)),
        }),
        forInductionNode: (nodeId: string) => ({
          ...makeAnyNodeActions(set, draft => getNodeOrThrow(draft, nodeId)),
          types: listFieldToInductionNodeStmtListActions(set, nodeId, "types"),
          motive: listFieldToInductionNodeStmtListActions(set, nodeId, "motive"),
          inductiveCases: listFieldToInductionNodeStmtListActions(set, nodeId, "inductiveCases"),
          baseCases: listFieldToInductionNodeStmtListActions(set, nodeId, "baseCases"),
          identifier: listFieldToInductionNodeStmtListActions(set, nodeId, "identifier"),
          ...makeInductionNodeActions(set, draft => getInductionNodeOrThrow(draft, nodeId)),
        }),
      }
      
    }
  })
);
