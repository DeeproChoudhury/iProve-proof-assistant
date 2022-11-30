import { SetStateAction } from "react";
import { Node } from "reactflow";
import { alt, apply, buildLexer, expectEOF, expectSingleResult, kmid, kright, Lexer, list_sc, nil, opt, Parser, rep_sc, rule, seq, str, tok, Token } from "typescript-parsec";
import { IProveError } from "../components/Flow";
import { ListField, StatementNodeType, InductionNodeType, StatementNodeData } from "../types/Node";
import { StatementType } from "../types/Statement";
import { applyAction, Setter } from "./setters";

export function localIndexToAbsolute(data: StatementNodeData, k: ListField<StatementNodeData>, index: number): number {
  switch (k) {
    case "givens": return index;
    case "proofSteps": return data.givens.length + index;
    case "goals": return data.givens.length + data.proofSteps.length + index;
  }
}

export function absoluteIndexToLocal(data: StatementNodeData, index: number): [ListField<StatementNodeData>, number] {
  if (index < data.givens.length) return ["givens", index];
  else if (index < data.givens.length + data.proofSteps.length) return ["proofSteps", index - data.givens.length];
  else return ["goals", index - data.givens.length - data.proofSteps.length];
}

export const setStatementsForNode = <K extends string, D extends Record<K, StatementType[]>, T extends Node<D>>(
  setNode: Setter<T>,
  k: K
) => (
  action: SetStateAction<StatementType[]>
) => {
  setNode(node => {
    return {
      ...node,
      data: {
        ...node.data,
        [k]: applyAction(action, node.data[k])
      }
    }
  });
};

export const setNodeWithId = <T extends StatementNodeType | InductionNodeType>(
  setNodes: Setter<T[]>,
  nodeId: string
) => (action: SetStateAction<T>) => {
  setNodes(nds => nds.map((nd) => nd.id === nodeId ? applyAction(action, nd) : nd));
};

export const collided = (node1: Node, node2: Node): boolean => {
  const a: number = node1.position.x - node2.position.x;
  const b: number = node1.position.y - node2.position.y;
  return Math.sqrt(a * a + b * b) < 100;
}

export const shiftReasonsForNode = (
  setNode: Setter<StatementNodeType>
) => (
  k: ListField<StatementNodeData>,
  index: number | undefined,
  offset: -1 | 1
) => {
  setNode(node => {
    const newNode = {
      ...node,
      data: {
        ...node.data,
        proofSteps: [...node.data.proofSteps],
        goals: [...node.data.goals]
      }
    }

    const defaultIndex = node.data[k].length;
    const changed = localIndexToAbsolute(node.data, k, index ?? defaultIndex);
    const start = Math.max(changed, newNode.data.givens.length); // givens don't need to be updated
    const end = newNode.data.givens.length + newNode.data.proofSteps.length + newNode.data.goals.length
    for (let i = start; i < end; i++) {
      const [field, relI] = absoluteIndexToLocal(newNode.data, i);
      const statement = newNode.data[field][relI];
      if (!statement.reason) continue;
      const newDeps = [...statement.reason.dependencies];
      for (let depIndex = 0; depIndex < newDeps.length; depIndex++) {
        if (newDeps[depIndex] >= changed) newDeps[depIndex] += offset;
      }
      newNode.data[field][relI] = {
        ...statement,
        reason: {
          ...statement.reason,
          dependencies: newDeps
        }
      }
    }
    return newNode;
  });
};

export const invalidateReasonForNode = (
  setNode: Setter<StatementNodeType>
) => (
  k: ListField<StatementNodeData>,
  index: number
) => {
  setNode(node => {
    const newNode = {
      ...node,
      data: {
        ...node.data,
        proofSteps: [...node.data.proofSteps],
        goals: [...node.data.goals]
      }
    }
    const changed = localIndexToAbsolute(newNode.data, k, index);
    const start = Math.max(changed, newNode.data.givens.length); // givens don't need to be updated
    const end = newNode.data.givens.length + newNode.data.proofSteps.length + newNode.data.goals.length
    for (let i = start; i < end; i++) {
      const [field, relI] = absoluteIndexToLocal(newNode.data, i);
      const statement = newNode.data[field][relI];
      if (!statement.reason) continue;
      const deps = statement.reason.dependencies;

      if (i === changed || deps.includes(changed)) {
        newNode.data[field][relI] = {
          ...statement,
          reason: {
            ...statement.reason,
            status: "unchecked"
          }
        }
      }
    }
    return newNode;
  });
};

export function renderError(E: IProveError): string {
  switch (E.kind) {
    case "Syntax": {
      let msg = E.msg ?? "Parsing for the last node failed"
      return E.pos?.column
        ? `${msg} - Detected at column ${E.pos.column}, in "${E.pos.statement.value}"`
        : `${msg} - Check your syntax!`
    }
    case "Proof":
      return E.pos?.statement
        ? `Validity check failed on statement ${E.pos.statement.value}, check your implications!`
        : `Validity check failed, check your implications!`
    case "Semantic":
      return E.pos?.statement
        ? `${E.subtype ?? "Error"} in ${E.pos.statement.value}: ${E.msg}`
        : (E.subtype ? `${E.subtype}: ${E.msg}` : (E.msg ?? ""))
    default:
      return E.msg ?? ""
  }
}

export function mk_error({
  kind = undefined,
  msg = undefined,
  subtype = undefined,
  statement = undefined,
  column = undefined
}:{
  kind?: "Syntax" | "Semantic" | "Proof",
  msg?: string,
  subtype?: string,
  statement?: StatementType,
  column?: number
}): IProveError {
  return {
    kind: kind,
    msg: msg,
    subtype: subtype,
    pos: (statement)
      ? { statement: statement, column: column}
      : undefined
  }
}

type ErrorToken = "(" | ")" | '"' | "Number" | "Word" | "Other" | "Space";
const error_lexer: Lexer<ErrorToken> = buildLexer([
  [true, /^\)/g, ")"],
  [true, /^\(/g, "("],
  [true, /^\"/g, "\""],
  [true, /^\d+/g, "Number"],
  [true, /^\w+/g, "Word"],
  [true, /^\S/g, "Other"],

  [false, /^(\s|\n)+/g, "Space"]
]);

const STRING = rule<ErrorToken, string>()
const Z3_ERRORS = rule<ErrorToken, (undefined | IProveError)[]>()
STRING.setPattern(apply(rep_sc(alt(tok("Word"), tok("Number"))),
    (v: Token<"Word" | "Number">[]): string =>
    v.map((x) => x.text).join(" ")))

Z3_ERRORS.setPattern(rep_sc(
  apply(
    kmid(
      tok("("), 
      kright(
        str("error"), 
        kmid(
          tok("\""),
          seq(
            opt(
              seq(
                kright(str("line"), tok("Number")),
                kmid(str("column"), tok("Number"), str(":"))
              )
            ),
            STRING
          ),
          tok("\"")
        )
      ),
      tok(")")
    ),
    (v: [[Token<"Number">, Token<"Number">] | undefined, string])
      : IProveError => (mk_error({
        kind: "Semantic",
        msg: v[1],
      }))
  )
))

export function parse_z3_error(e: string): IProveError | undefined {
  let A = Z3_ERRORS.parse(error_lexer.parse(e));
  if (!A.successful) return;
  return expectSingleResult(A)[0];
}
