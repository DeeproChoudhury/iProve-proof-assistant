/*
    Display Functions
*/

function fnDisplay(fn: string): string {
    switch (fn) {
        case "~": return "¬"; 
        case "&": return "∧";
        case "|": return "∨";
        case "^": return "⊕";
        case "->": return "→";
        case "<->": return "↔";
        default: return fn;
    }
}

function fnSMT(fn: string): string {
    switch (fn) {
        case "~": return "not";
        case "&": return "and";
        case "|": return "or";
        case "^": return "xor";
        case "->": return "implies";
        case "<->": return "=";
        default: return fn;
    }
}

/*
    Unifcation scope functions
*/

export function get_from_scope(S: UnifyScope, x: string): string | undefined {
    for (let ss of S.assignments) {
        if (ss.has(x)) return ss.get(x)
    }
}

export function set_in_scope(S: UnifyScope, a: string, b: string): boolean {
    if (S.sort_ctx_a.get(a) != S.sort_ctx_b.get(b)) return false
    S.assignments[0].set(a, b)
    return true
}

export function push_scope(S: UnifyScope): void {
    S.assignments.unshift(new Map)
}

export function pop_scope(S: UnifyScope): void {
    S.assignments.shift()
}

/*
    Bitmap functions for DP/Recursion
*/

export function bitmap_mex(bs: number, st: number = 0): number {
    bs = bs >> st
    let R = st;
    while (bs & 1) {
        R++;
        bs = bs >> 1;
    }
    return R
}

export function set_bit(N: number, i: number): number {
    return N | (1 << i)
}

/*
    Complexity safety functions
*/

function assoc_length(A: Term, c: number): [Term, number] {
    return [A, (A.kind == "FunctionApplication" && AssocOperators.has(A.fn))
        ? Math.max(A.params.length, c)
        : c]
}
const mapped_AL = map_terms(assoc_length, 0)
export const max_assoc_length = (x: Term): number => mapped_AL(x)[1]