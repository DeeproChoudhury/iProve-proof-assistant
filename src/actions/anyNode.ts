import { current, Draft } from "immer";
import { ActionContext, actionsWithContext } from '../store/ActionContext';
import { IProveDraft } from '../store/store';
import { AnyNodeType, InductionNodeType, ListField, StatementNodeType } from '../types/Node';
import { parseAll as parseAllStatements } from "./statementList";
import { mutual_rec_on } from "../logic/induction";
import { Line, TypeDef, QuantifierApplication, VariableBinding, Variable, Term, Type, ASTNode } from "../types/AST";
import { unwrap_statements } from "../util/statements";

import { isTerm, conjunct, imply, range_over_bindings, display, iff } from "../util/trees";
import { getInputs, getOutputs, narrowNodeCtx } from "../util/nodes";

import { LIQ } from "../logic/LogicInterfaceQueue";
import { invalidateInternals } from "./inductionNode";
import { recheckReasons, setWrappers } from "./statementNode";
import { mk_error } from "../util/errors";

export const parseAll = (ctx: ActionContext<AnyNodeType>) => {
  ctx.setError(undefined);
  const narrow = narrowNodeCtx(ctx);

  if (narrow.kind === "statementNode") {
    (["givens", "proofSteps", "goals"] as const)
      .forEach(listField => parseAllStatements(narrow.ctx.composeLens(node => node.data[listField])));
  }

  if (narrow.kind === "inductionNode") {
    (["types", "motive", "inductiveCases", "baseCases", "identifier"] as const)
      .forEach(listField => parseAllStatements(narrow.ctx.composeLens(node => node.data[listField])));
  }
}

export const checkInternal = (ctx_: ActionContext<AnyNodeType>) => {
  const narrow = narrowNodeCtx(ctx_);
  if (narrow.kind === "statementNode") {
    recheckReasons(narrow.ctx);
    return;
  }
  const ctx = narrow.ctx;

  const node = ctx.draft;

  node.data.internalsStatus = "checking";

  let types: Line[] = unwrap_statements(node.data.types)
  //   :/
  if (types.some(x => x.kind != "TypeDef")) return;
  let tdefs: TypeDef[] = (types as TypeDef[])

  let motives_: Line[] = unwrap_statements(node.data.motive)
  if (motives_.some(x => x.kind != "QuantifierApplication" || !x.vars.length || x.quantifier == "E")) {
    ctx.setError({
      kind: "Semantic",
      msg: "Induction motive must begin by ranging over inductively defined type",
      status: "error"
    });
    node.data.internalsStatus = "invalid";
    return;
  }
  if (motives_.some(x => x.kind == "QuantifierApplication" && x.vars[0].type?.kind == "PrimitiveType" && x.vars[0].bound == undefined && x.vars[0].type?.ident == "Int")) {
    ctx.setError({
      kind: "Semantic",
      msg: "Unbounded integers are not inductive types",
      status: "error"
    });
    node.data.internalsStatus = "invalid";
    return;
  }

  
  let motives: QuantifierApplication[] = motives_ as QuantifierApplication[]
  let vbinds: VariableBinding[] = motives.map(m => m.vars[0])
  let identifiers: Variable[] = vbinds.map(v => v.symbol)
  let tidents_: (Type | undefined)[] = vbinds.map(v => v.type)
  if (tidents_.some(t => !t)) return;
  let tidents: Type[] = tidents_ as Type[]

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

  let cases: Line[] = unwrap_statements(node.data.baseCases.concat(node.data.inductiveCases))
  for (let c of cases) {
    if (!isTerm(c)) {
      ctx.setError(mk_error({
        kind: "Semantic",
        msg: "Inductive terms must be first-order formulae!"
      }));
      node.data.internalsStatus = "invalid";
      return;
    }
  }

  let precond: Term | undefined = conjunct(cases as Term[])
  let cum_motives = conjunct(final_motives)
  if (!cum_motives) {
    ctx.setError(mk_error({
      kind: "Semantic",
      msg: "Inductive terms must be first-order formulae!"
    }));
    node.data.internalsStatus = "invalid";
    return;
  }


  let tidentifiers = identifiers.map(
    (v, i): [Variable, Type] => [v, tidents[i] as Type])
  let IP: Term = (precond)
    ? imply(precond, range_over_bindings(cum_motives, vbinds))
    : range_over_bindings(cum_motives, vbinds)

  let gt_IP: Term = mutual_rec_on(tdefs)(motives.map((m) => m.vars[0]), final_motives)
  
  console.log("GT", display(gt_IP))
  console.log("USER", display(IP))

  LIQ.queueEntails([], iff(IP, gt_IP), ctx.newAction((ctx, verdict) => {
    let success = (verdict.kind === "Valid")

    if (success) {
      ctx.draft.data.internalsStatus = "valid";
    } else {
      ctx.setError(undefined)
      ctx.draft.data.internalsStatus = "invalid";
    }
  }), true, true);
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

  const ctxStatementNode = ctx.narrowType((node): node is Draft<StatementNodeType> => node.type !== "inductionNode")
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
