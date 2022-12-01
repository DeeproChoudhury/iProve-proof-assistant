import * as AST from "./AST"


export type PatternElem = {
    kind: "Condition" | "Binding",
    value: string
}
export type PatternData = PatternElem[]

export type FunctionData = {
    decl: AST.FunctionDeclaration | undefined,
    cid: number,
    defs: Map<number, AST.FunctionDefinition>
}

export type StatefulTransformer<T, S> = (x: T, st: S) => [T, S]


export class IdentState {
    cid: number = 0;
    get(): number {
        return this.cid++;
    }
}

export type RenameState = Map<string, number>

export type Unification = UnifyFail | UnifyScope
export type UnifyFail = { kind: "UnifyFail" }

export type UnifyScope = {
    kind: "UnifyScope";
    sort_ctx_a: Map<string, string>;
    sort_ctx_b: Map<string, string>;
    assignments: Map<string, string | undefined>[];
}

export type AlphaAssignment = {
    kind: "AlphaAssignment",
    assn: Map<string, string>,
    term: AST.Term
}
