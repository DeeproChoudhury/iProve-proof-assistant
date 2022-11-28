import * as AST from "../types/AST"
import { RenameState } from "../types/LogicInterface"
import { mk_var, seek_parens } from "../util/trees"
import { map_terms, stateless_map_terms } from "./combinator"

export const AssocOperators: Set<string> = new Set([
    "&",
    "||"
])

export const CommOperators: Set<string> = new Set([
    "&",
    "||"
])

/**
 * Given an AST Term, if it's a quantifier whose child term is a quantifier
 * of the same type, then the term and its child will be merged
 * 
 * @param A - The term to squash
 * @returns The squashed term
 * 
 */
function squash_quantifier(A: AST.Term): AST.Term {
    return (
        A.kind == "QuantifierApplication"
        && A.term.kind == "QuantifierApplication"
        && A.quantifier == A.term.quantifier
    ) ? {
        kind: "QuantifierApplication",
        term: A.term.term,
        vars: A.vars.concat(A.term.vars),
        quantifier: A.quantifier
    } : A
}

/**
 * This function merges all adjacent quantifiers in a term into each other by
 * concatenating their variable bindings
 * 
 * @param A - The term to squash
 * @returns The squashed term
 * 
 */
export const squash_quantifiers = stateless_map_terms(squash_quantifier)

/**
 * This is the private single-term function from which extract_assoc is
 * built
 * 
 * @param A             - The term to merge
 * @param ignore_parens - The merge-through-parens flag
 * @returns The merged term
 * 
 */
function assoc_chain(A: AST.Term, ignore_parens: Boolean = false): AST.Term {
    return (
        A.kind == "FunctionApplication"
        && A.appType != "ArrayElem" && A.appType != "ArraySlice"
        && AssocOperators.has(A.fn)
    ) ? {
        kind: "FunctionApplication",
        appType: "PrefixOp",
        fn: A.fn,
        params: A.params.map((sub: AST.Term): AST.Term[] => {
            let w_sub: AST.Term = (ignore_parens) ? seek_parens(sub) : sub
            return (w_sub.kind == "FunctionApplication"
                && w_sub.appType != "ArrayElem" && w_sub.appType != "ArraySlice"
                && A.fn == w_sub.fn)
            ? w_sub.params
            : [sub]
        }).flat()
    } : A
}

/**
 * An associative chain is any repeated application of associative binary
 * operators. This function, given an ignore_parens flag, returns a function which
 * extracts them into a single application to many arguments.
 *
 * @remarks
 * 
 * If `ignore_parens` is set, then associativity will actually be exploited
 * in the reduction by ignoring any explicit parenthesisation of terms. Otherwise
 * this will be respected, only flattening out structure imposed by the term
 * parser itself.
 * In the way we're using it, it that we are exploiting associativity of (& / |),
 * whereas disabling it allows us to account for commutativity without exploiting
 * associativity
 * 
 * @param ignore_parens - The merge-through-parens flag
 * @returns The merging function
 * 
 */
export function extract_assoc(ignore_parens: Boolean = false)
: (x: AST.Term) => AST.Term {
    return stateless_map_terms((x_: AST.Term): AST.Term => assoc_chain(x_, ignore_parens))
} 

/**
 * Given a 0-ary function application, will return a variable of the same
 * identifier
 * 
 * @param A - The term to normalize
 * @returns The normalized term
 * 
 */
function variablize(A: AST.Term): AST.Term {
    return (A.kind == "FunctionApplication"
        && (A.appType == "PrefixFunc"
            || A.appType == "PrefixOp"
            || A.appType == "UnaryFunc"
            || A.appType == "UnaryOp")
        && (!A.params.length))
        ? {
           kind: "Variable",
           ident: A.fn
        }
        : A
}
/**
 * Given a term, will normalize all instances of 0-ary function application to
 * variable nodes
 * 
 * @param A - The term to normalize
 * @returns The normalized term
 * 
 */
export const normalize_constants = stateless_map_terms(variablize);

/**
 * Removes parentheses from a ParenTerm
 * 
 * @param A - The term to normalize
 * @returns The normalized term
 * 
 */
function unparenthesize(A: AST.Term): AST.Term {
    return (A.kind == "ParenTerm")
        ? A.term
        : A
}
/**
 * Given a term, will remove all explicit parentheses, since these are not
 * required (other than for display purposes) once the AST is built from input
 * 
 * @param A - The term to normalize
 * @returns The normalized term
 * 
 */
export const remove_parens = stateless_map_terms(unparenthesize)

/**
 * The constituent function for renaming_pass. Given a term and a state
 * counting the nested occurrences of each identifier as a bound variable up
 * to this depth in the AST, appropriately renames any identifiers in a
 * QuantifierApplication or Variable node
 * 
 * @param A - The term to rename
 * @param S - The current renaming state
 * @returns A pair of the renamed term, and state updated to reflect new identifiers
 * 
 */
function rename_vars(A: AST.Term, S: RenameState): [AST.Term, RenameState] {
    switch(A.kind) {
        case "ArrayLiteral":
        case "EquationTerm":
        case "FunctionApplication":
        case "ParenTerm":
            return [A, S]

        case "QuantifierApplication": {
            let nvd: AST.VariableBinding[] = []
            for (let v of A.vars) {
                let VI = S.get(v.symbol.ident)
                if (VI && VI > 0) {
                    nvd.push({
                        kind: "VariableBinding",
                        symbol: mk_var(`IProveAlpha_${VI}_${v.symbol.ident}`),
                        type: v.type
                    })
                    S.set(v.symbol.ident, VI + 1)
                } else {
                    nvd.push({
                        kind: "VariableBinding",
                        symbol: mk_var(`IProveAlpha_0_${v.symbol.ident}`),
                        type: v.type
                    })
                    S.set(v.symbol.ident, 1)
                }
            }
            return [{
                kind: "QuantifierApplication",
                quantifier: A.quantifier,
                term: A.term,
                vars: nvd
            }, S]
        }
        case "Variable": {
            let VI = S.get(A.ident)
            if (VI && VI > 0)
                return [mk_var(`IProveAlpha_${VI - 1}_${A.ident}`), S]
            else
                return [A, S]
        }
    }
}

/**
 * Given a term, will rewrite all bound variables such that they have unique
 * identifiers which cannot conflict with free variables.
 * 
 * @param A - The term to rename
 * @returns The term after a renaming pass
 * 
 */
export function rename_pass(A: AST.Term): AST.Term
    { return map_terms(rename_vars, new Map, true)(A)[0]; }

/**
 * Given a term, nondestructively normalizes by squashing quantifiers,
 * renaming bound variables, and normalizing 0-ary functions
 * 
 * @param A - The term to process
 * @returns The term after processing
 * 
 */
export function basic_preprocess(A: AST.Term): AST.Term {
    return squash_quantifiers(
        rename_pass (
            normalize_constants(A)
        )
    )
}

/**
 * Given a term, prepares it for unification by performing basic_preprocess
 * followed by removing all parentheses and merging associative chains
 * 
 * @param A - The term to process
 * @returns The term after processing
 * 
 */
export function unify_preprocess(A: AST.Term): AST.Term {
    return extract_assoc()(
        remove_parens(
            basic_preprocess(A)
        )
    )
}

const alpha_regex: RegExp = /^IProveAlpha_(\d+)_/
/**
 * Given a map from strings to strings, returns the simplifier function
 * which replaces all occurences of identifiers in the keys of `M` with
 * their value in `M`
 * 
 * @param M - The identifier renaming lookup table
 * @param unalpha - If set, this function will also undo rename_vars processing
 *                  (default: true) 
 * @returns The term after renaming
 * 
 */
function replace_var(M: Map<string, string>, unalpha: boolean = true): (A: AST.Term) => AST.Term {
    let MGet_ = (xi: string): string =>
        { let R = M.get(xi); return (R) ? R : xi; }
    let MGet = (xi: string): string => 
        (unalpha) ? MGet_(xi) : MGet_(xi)?.replace(alpha_regex, '')
    return (A: AST.Term): AST.Term => {
        switch (A.kind) {
            case "ArrayLiteral":
            case "EquationTerm":
            case "FunctionApplication":
            case "ParenTerm":
                return A
            
            case "QuantifierApplication": {
                let VL: AST.VariableBinding[] = []
                for (let vb of A.vars) {
                    VL.push({
                        kind: "VariableBinding",
                        symbol: mk_var(MGet(vb.symbol.ident)),
                        type: vb.type
                    })
                }
                return {
                    kind: "QuantifierApplication",
                    term: A.term,
                    quantifier: A.quantifier,
                    vars: VL
                }
            }
            case "Variable":
                return mk_var(MGet(A.ident))

        }
    }
}
export function replace_vars(M: Map<string, string>, unalpha: boolean = false): (x: AST.Term) => AST.Term {
    return stateless_map_terms(replace_var(M, unalpha))
}