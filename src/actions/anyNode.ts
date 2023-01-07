import { current, Draft } from "immer";
import { ActionContext, actionsWithContext } from '../store/ActionContext';
import { IProveDraft } from '../store/store';
import { AnyNodeType, InductionNodeType, ListField, StatementNodeType } from '../types/Node';
import { parseAll as parseAllStatements } from "./statementList";
import { mutual_rec_on } from "../logic/induction";
import { unifies } from "../logic/unifier";
import { Line, TypeDef, QuantifierApplication, VariableBinding, Variable, Term, Type } from "../types/AST";
import { unwrap_statements } from "../util/statements";
import { isTerm, conjunct, imply, range_over, display } from "../util/trees";
import { getInputs, getOutputs } from "../util/nodes";
import { LIQ } from "../logic/LogicInterfaceQueue";
import { invalidateInternals } from "./inductionNode";
import { setWrappers } from "./statementNode";

export const parseAll = (ctx: ActionContext<AnyNodeType>) => {
  ctx.setError(undefined);

  const ctxStatementNode = ctx.narrowType((node): node is Draft<StatementNodeType>  => node.type !== "inductionNode")
  if (ctxStatementNode) {
    (["givens", "proofSteps", "goals"] as const)
      .forEach(listField => parseAllStatements(ctxStatementNode.composeLens(node => node.data[listField])));
  }

  const ctxInductionNode = ctx.narrowType((node): node is Draft<InductionNodeType>  => node.type === "inductionNode")
  if (ctxInductionNode) {
    (["types", "motive", "inductiveCases", "baseCases", "identifier"] as const)
      .forEach(listField => parseAllStatements(ctxInductionNode.composeLens(node => node.data[listField])));
  }
}

export const checkInternal = (ctx_: ActionContext<AnyNodeType>) => {
  const ctx = ctx_.narrowType((node): node is Draft<InductionNodeType>  => node.type === "inductionNode")
  if (!ctx) return; // nothing to do for statement nodes

  const node = ctx.draft;

  node.data.internalsStatus = "checking";

  let types: Line[] = unwrap_statements(node.data.types)
  //   :/
  if (types.some(x => x.kind != "TypeDef")) return;
  let tdefs: TypeDef[] = (types as TypeDef[])

  let motives_: Line[] = unwrap_statements(node.data.motive)
  if (motives_.some(x => x.kind != "QuantifierApplication" || !x.vars.length))
    return;
  let motives: QuantifierApplication[] = motives_ as QuantifierApplication[]
  let vbinds: VariableBinding[] = motives.map(m => m.vars[0])
  let identifiers: Variable[] = vbinds.map(v => v.symbol)
  let tidents_: (Type | undefined)[] = vbinds.map(v => v.type)
  if (tidents_.some(t => !t)) return;
  let tidents: Type[] = tidents_ as Type[]

  console.log("PREM", motives)
  let final_motives = motives.map((m): Term =>
    (m.vars.length < 2)
      ? m.term
      : {
        kind: "QuantifierApplication",
        term: m.term,
        vars: m.vars.slice(1),
        quantifier: m.quantifier
      }
  )

  console.log("RAW CASES", node.data.baseCases, node.data.inductiveCases)
  let cases: Line[] = unwrap_statements(node.data.baseCases.concat(node.data.inductiveCases))
  for (let c of cases) {
    console.log("HERE C", c)
    if (!isTerm(c)) {
      ctx.setError({
        kind: "Semantic",
        msg: "Inductive terms must be first-order formulae!"
      });
      node.data.internalsStatus = "invalid";
      return;
    }
  }

  let precond: Term | undefined = conjunct(cases as Term[])
  let cum_motives = conjunct(final_motives)
  console.log("CMOTIVE", cum_motives, final_motives)
  if (!cum_motives) {
    ctx.setError({
      kind: "Semantic",
      msg: "Inductive terms must be first-order formulae!"
    });
    node.data.internalsStatus = "invalid";
    return;
  }

  let tidentifiers = identifiers.map(
    (v, i): [Variable, Type] => [v, tidents[i] as Type])
  let IP: Term = (precond)
    ? imply(precond, range_over(cum_motives, tidentifiers))
    : range_over(cum_motives, tidentifiers)

  let gt_IP: Term = mutual_rec_on(tidents, tdefs)(identifiers.map(x=>x.ident), final_motives)
  
  console.log("GT", display(gt_IP))
  console.log("USER", display(IP))
  let verdict = unifies(IP, gt_IP)
  if (!verdict) {
    ctx.setError(undefined)
    node.data.internalsStatus = "invalid";
    return;
  }

  console.log("VERDICT", display(verdict.term))
  node.data.internalsStatus = "valid";
}

export const checkEdges = (ctx: ActionContext<AnyNodeType>) => {
  const currEdges = ctx.replaceLens(draft => draft.edges).draft;
  const currNodes = ctx.replaceLens(draft => draft.nodes).draft;
  const node = ctx.draft;

  const incomingEdges = currEdges.filter((e) => e.target === node.id);
  const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
  const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
  const givens = incomingNodes.flatMap(getOutputs);
  const expImplications = getInputs(node);
  if (expImplications.some(s => !s.parsed)) {
    return; // TODO: show error message here
  }
  let success: boolean = false;

  let goal: Term | undefined = conjunct(unwrap_statements(expImplications))
  if (!goal) return;
   
  LIQ.queueEntails(unwrap_statements(givens), goal, ctx.newAction((ctx, verdict) => {
    success = (verdict.kind === "Valid")

    ctx.draft.data.edgesStatus = success ? "valid" : "invalid"

    ctx.replaceLens(draft => draft.edges).draft.forEach(edge => {
      if (edge.target === ctx.draft.id)
        edge.type = success ? "checked" : "invalid";
    })
  }));
}

export const invalidateEdges = (ctx: ActionContext<AnyNodeType>) => {
  const node = ctx.draft;
  node.data.edgesStatus = "unchecked";
  const edges = ctx.replaceLens(draft => draft.edges).draft;
  for (const edge of edges) {
    if (edge.target === node.id) {
      edge.type = "unchecked";
    }
  }
};

export const invalidateOutgoingEdges = (ctx: ActionContext<AnyNodeType>) => {
  const node = ctx.draft;
  const edges = ctx.replaceLens(draft => draft.edges).draft;
  for (const edge of edges) {
    if (edge.source === node.id) {
      edge.type = "unchecked";
    }
  }
};

export const recheck = (ctx: ActionContext<AnyNodeType>, listField: ListField<AnyNodeType["data"]>, updated: number): void => {
  parseAll(ctx);

  const ctxStatementNode = ctx.narrowType((node): node is Draft<StatementNodeType>  => node.type !== "inductionNode")
  if (ctxStatementNode) {
    switch (ctxStatementNode.draft.type) {
      case "givenNode":
        invalidateOutgoingEdges(ctxStatementNode);
        break;
      case "proofNode":
        if (listField === "givens") invalidateEdges(ctxStatementNode);
        if (listField === "proofSteps") setWrappers(ctxStatementNode);
        if (listField === "goals") invalidateOutgoingEdges(ctxStatementNode);
        break;
      case "goalNode":
        invalidateEdges(ctxStatementNode);
        break;

    }
  }
  
  const ctxInductionNode = ctx.narrowType((node): node is Draft<InductionNodeType>  => node.type === "inductionNode")
  if (ctxInductionNode) {
    invalidateInternals(ctxInductionNode);
    switch (listField as ListField<InductionNodeType["data"]>) {
      case "baseCases":
      case "inductiveCases":
        invalidateEdges(ctxInductionNode);
        break;
      case "motive":
        invalidateOutgoingEdges(ctxInductionNode);
    }
  }
}

const actions = {
  parseAll, checkInternal, checkEdges, invalidateEdges, invalidateOutgoingEdges, recheck
} as const;

export const makeAnyNodeActions = (set: (cb: (draft: IProveDraft) => void) => void, lens: (draft: IProveDraft) => Draft<AnyNodeType>) => {
  return actionsWithContext<keyof typeof actions, AnyNodeType, typeof actions>(set, actions, lens);
}
