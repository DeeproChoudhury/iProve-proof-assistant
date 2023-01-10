import { LIQ } from '../logic/LogicInterfaceQueue';
import { ActionContext, actionsWithContext } from '../store/ActionContext';
import { IProveDraft, StoreType, UIComponentName } from '../store/store';
import { Line } from '../types/AST';
import { NodeKind } from '../types/Node';
import { StatementType } from '../types/Statement';
import { mk_error } from '../util/errors';
import { allParsed, edgesStatus, internalsStatus, narrowNodeCtx } from '../util/nodes';
import { isTerm } from '../util/trees';
import { checkEdges, checkInternal, parseAll } from './anyNode';
import { autoAddReasons } from './statementNode';

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

export const addImportedProof = ({ draft }: ActionContext<StoreType>, json: any) => {
  // Create Given, Proof, Goal Nodes from input data
  draft.nodes = json.nodes.map((node: any) => {
    const id = node.id;
    draft.nextNodeId++;

    if (node.type === "inductionNode") {
      return {
        id: `${id}`,
        data: {
          label: node.data.label,
          internalsStatus: "unchecked",
          edgesStatus: node.data.edgesStatus,
          types: node.data.types,

          inductiveCases: node.data.inductiveCases,
          baseCases: node.data.baseCases,
          motive: node.data.motive,
          identifier: node.data.identifier,

        },
        position: node.position,
        type: node.type,
      }
    } else {
      const n = node;
      n.data.edgesStatus = node.data.edgesStatus;
      return n;
    }
  });
  
  draft.edges = json.edges.map((edge: any) => {
    const e = edge;
    e.type = edge.type;
    return e;
  })

  draft.declarations = json.declarations;
  draft.typeDeclarations = json.types;

}

export const showUI = (ctx: ActionContext<StoreType>, name: UIComponentName) => {
  ctx.draft.uiShown[name] = true;
}

export const hideUI = (ctx: ActionContext<StoreType>, name: UIComponentName) => {
  ctx.draft.uiShown[name] = false;
}

export const toggleUI = (ctx: ActionContext<StoreType>, name: UIComponentName) => {
  ctx.draft.uiShown[name] = !ctx.draft.uiShown[name];
}

export const startVerifyProofGlobal = (ctx: ActionContext<StoreType>) => {
  const anyMissingReasons = ctx.draft.nodes.some(node => {
    if (node.type !== "proofNode") return false;
    return [...node.data.proofSteps, ...node.data.goals]
      .filter(statement => statement.parsed && isTerm(statement.parsed))
      .some(statement => !statement.reason || statement.reason.status !== "valid" );
  });
  if (anyMissingReasons) showUI(ctx, "addReasons");
  else verifyProofGlobal(ctx);
}

export const verifyProofGlobal = (ctx: ActionContext<StoreType>) => {
  for (let i = 0; i < ctx.draft.nodes.length; i++) {
    const nodeCtx = ctx.composeLens(draft => draft.nodes[i])
    parseAll(nodeCtx)
    const narrow = narrowNodeCtx(nodeCtx);
    if (narrow.kind === "statementNode") {
      autoAddReasons(narrow.ctx);
    }
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
  addGivenNode, addProofNode, addGoalNode, addInductionNode, deleteNode, addImportedProof, showUI, hideUI, toggleUI, verifyProofGlobal, resetError
} as const;

export const makeGlobalActions = (set: (cb: (draft: IProveDraft) => void) => void) => {
  return actionsWithContext<keyof typeof actions, StoreType, typeof actions>(set, actions, draft => draft);
}
