import { applyNodeChanges, Node } from 'reactflow';
import { LIQ } from '../logic/LogicInterfaceQueue';
import { ActionContext, actionsWithContext } from '../store/ActionContext';
import { IProveDraft, StoreType } from '../store/store';
import { IProveError } from '../types/ErrorLocation';
import { NodeKind } from '../types/Node';
import { StatementType } from '../types/Statement';
import { allParsed, edgesStatus, internalsStatus } from '../util/nodes';
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
          edgesStatus: "unchecked",
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
      n.data.edgesStatus = "unchecked";
      return n;
    }
  });
  
  draft.edges = json.edges.map((edge: any) => {
    const e = edge;
    e.type = "implication";
    return e;
  })

  draft.declarations = json.declarations;
  draft.typeDeclarations = json.types;

}

export const verifyProofGlobal = (ctx: ActionContext<StoreType>) => {
  for (let i = 0; i < ctx.draft.nodes.length; i++) {
    const nodeCtx = ctx.composeLens(draft => draft.nodes[i])
    parseAll(nodeCtx)
    checkInternal(nodeCtx);
    checkEdges(nodeCtx);
  }
  LIQ.queue(ctx.newAction(ctx => {
    const internalsValid = ctx.draft.nodes.every(node => allParsed(node) && internalsStatus(node) === "valid");
    const edgesValid = ctx.draft.nodes.every(node => allParsed(node) && edgesStatus(node) === "valid");
    // if problem is with edges don't show anything as there are other errors being displayed
    if (edgesValid && internalsValid) {
      ctx.draft.proofStatus = "valid";
    }
    if (edgesValid && !internalsValid) {
      ctx.draft.proofStatus = "invalid";
    }
  }));
}

export const resetError = (ctx: ActionContext<StoreType>) => {
  ctx.draft.error = undefined;
}

export const resetProofStatus = (ctx: ActionContext<StoreType>) => {
  ctx.draft.proofStatus = "unchecked";
}


const actions = {
  addGivenNode, addProofNode, addGoalNode, addInductionNode, deleteNode, addImportedProof, verifyProofGlobal, resetError, resetProofStatus
} as const;

export const makeGlobalActions = (set: (cb: (draft: IProveDraft) => void) => void) => {
  return actionsWithContext<keyof typeof actions, StoreType, typeof actions>(set, actions, draft => draft);
}
