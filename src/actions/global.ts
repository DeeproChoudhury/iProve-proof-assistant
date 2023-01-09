import { LIQ } from '../logic/LogicInterfaceQueue';
import { ActionContext, actionsWithContext } from '../store/ActionContext';
import { IProveDraft, StoreType } from '../store/store';
import { ExportedProof } from '../types/exported';
import { NodeKind } from '../types/Node';
import { StatementType } from '../types/Statement';
import { mk_error } from '../util/errors';
import { allParsed, edgesStatus, internalsStatus, stripPropertiesForExport } from '../util/nodes';
import { checkEdges, checkInternal, parseAll } from './anyNode';

const blankStatement: StatementType = { value: "", wrappers: [] };

export const addGivenNode = ({ draft }: ActionContext<StoreType>) => addNode(draft, "givenNode");
export const addProofNode = ({ draft }: ActionContext<StoreType>) => addNode(draft, "proofNode");
export const addGoalNode = ({ draft }: ActionContext<StoreType>) => addNode(draft, "goalNode");

const addNode = (draft: IProveDraft, kind: Exclude<NodeKind, "inductionNode">) => {
  const id = draft.nextNodeId.toString();
  draft.nodes.push({
    id,
    position: { x: 300, y: 0 },
    type: kind,
    data: {
      label: `Node ${id}`,
      edgesStatus: "unchecked",
      givens: [],
      proofSteps: [],
      goals: kind === "goalNode" ? [] : [blankStatement],
    }
  });
  draft.nextNodeId++;

}

export const addInductionNode = ({ draft }: ActionContext<StoreType>) => {
  const id = draft.nextNodeId.toString();
  draft.nodes.push({
    id,
    position: { x: 300, y: 0 },
    type: "inductionNode",
    data: {
      label: `Node ${id}`,
      edgesStatus: "unchecked",
      internalsStatus: "unchecked",
      types: [blankStatement],
      identifier: [blankStatement],
      inductiveCases: [],
      baseCases: [],
      motive: [blankStatement],
    }
  });
  draft.nextNodeId++;
};

export const deleteNode = ({ draft }: ActionContext<StoreType>, nodeId: string) => {
  draft.nodes = draft.nodes.filter(node => node.id !== nodeId);
};

export const importProofFromString = ({ draft }: ActionContext<StoreType>, json: string) => {
  // Create Given, Proof, Goal Nodes from input data
  const imported: ExportedProof = stripPropertiesForExport(JSON.parse(json));
  draft.nodes = imported.nodes;
  draft.edges = imported.edges;
  draft.declarations = imported.declarations;
  draft.typeDeclarations = imported.types;
  draft.nextNodeId = imported.nextNodeId;
}

export const verifyProofGlobal = (ctx: ActionContext<StoreType>) => {
  for (let i = 0; i < ctx.draft.nodes.length; i++) {
    const nodeCtx = ctx.composeLens(draft => draft.nodes[i])
    parseAll(nodeCtx)
    checkInternal(nodeCtx);
    checkEdges(nodeCtx);
  }
  LIQ.queue(ctx.newAction(ctx => {
    if (!ctx.draft.nodes.every(node => allParsed(node) && internalsStatus(node) === "valid")) {
      ctx.setError(mk_error({ kind: "Proof", msg: "Not all nodes valid" }));
    } else if (!ctx.draft.nodes.every(node => allParsed(node) && edgesStatus(node) === "valid")) {
      ctx.setError(mk_error({ kind: "Proof", msg: "Not all edges valid" }));
    } else {
      ctx.setError(mk_error({ kind: "Proof", status: "success" }));
    }
  }));
}

export const resetError = (ctx: ActionContext<StoreType>) => {
  ctx.draft.error = undefined;
}

const actions = {
  addGivenNode, addProofNode, addGoalNode, addInductionNode, deleteNode, addImportedProof: importProofFromString, verifyProofGlobal, resetError
} as const;

export const makeGlobalActions = (set: (cb: (draft: IProveDraft) => void) => void) => {
  return actionsWithContext<keyof typeof actions, StoreType, typeof actions>(set, actions, draft => draft);
}
