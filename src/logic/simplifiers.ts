const AssocOperators: Set<string> = new Set([
    "&",
    "||"
])

const CommOperators: Set<string> = new Set([
    "&",
    "||"
])

// TODO: this function should be able to squash quantifiers down when what they
// quantify over only appears in one parameter of a function application
// but this requires leaf->root recursion over AST (or gross memoization :/)
// EDIT: Because JS isn't lazy, our recursion actually IS leaf-> root so now
// I've added a state to thread through this can get refactored
// EDIT: Need to think more about what allowing Prop-valued parameters
// does to our ability to do this in a PNF-syle.
function squash_quantifier(A: Term): Term {
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
export const squash_quantifiers = stateless_map_terms(squash_quantifier)

// An associative chain is any repeated application of associative binary
// operators. This function extracts them either with the ignore_parens
// flag set to false (in which case this simply flattens nested left-associative)
// applications), or true (in which case this flattens THROUGH parentheses).
//
// In the way we're using it, ignore_parens means that we are exploiting
// associativity of (& / | / +(over ints) / *(over ints)), whereas disabling
// it allows us to account for commutativity without exploiting associativity
function assoc_chain(A: Term, ignore_parens: Boolean = false): Term {
    return (
        A.kind == "FunctionApplication"
        && A.appType != "ArrayElem" && A.appType != "ArraySlice"
        && AssocOperators.has(A.fn)
    ) ? {
        kind: "FunctionApplication",
        appType: "PrefixOp",
        fn: A.fn,
        params: A.params.map((sub: Term): Term[] => {
            let w_sub: Term = (ignore_parens) ? seek_parens(sub) : sub
            return (w_sub.kind == "FunctionApplication"
                && w_sub.appType != "ArrayElem" && w_sub.appType != "ArraySlice"
                && A.fn == w_sub.fn)
            ? w_sub.params
            : [sub]
        }).flat()
    } : A
}
export function extract_assoc(ignore_parens: Boolean = false)
: (x: Term) => Term {
    return stateless_map_terms((x_: Term): Term => assoc_chain(x_, ignore_parens))
} 

// 0-ary functions can be normalized to variables
function variablize(A: Term): Term {
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
export const normalize_constants = stateless_map_terms(variablize);

// Once in the AST, we can remove all unneccessary parens
function unparenthesize(A: Term): Term {
    return (A.kind == "ParenTerm")
        ? A.term
        : A
}
export const remove_parens = stateless_map_terms(unparenthesize)

function rename_vars(A: Term, S: RenameState): [Term, RenameState] {
    switch(A.kind) {
        case "ArrayLiteral":
        case "EquationTerm":
        case "FunctionApplication":
        case "ParenTerm":
            return [A, S]

        case "QuantifierApplication": {
            let nvd: VariableBinding[] = []
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

export function rename_pass(A: Term): Term
    { return map_terms(rename_vars, new Map, true)(A)[0]; }

export function basic_preprocess(A: Term): Term {
    return squash_quantifiers(
        rename_pass (
            normalize_constants(A)
        )
    )
}

export function unify_preprocess(A: Term): Term {
    return extract_assoc()(
        remove_parens(
            basic_preprocess(A)
        )
    )
}

const alpha_regex: RegExp = /^IProveAlpha_(\d+)_/
function replace_var(M: Map<string, string>, unalpha: boolean = true): (A: Term) => Term {
    let MGet = (xi: string): string | undefined => 
        (unalpha) ? M.get(xi) : M.get(xi)?.replace(alpha_regex, '')
    return (A: Term): Term => {
        switch (A.kind) {
            case "ArrayLiteral":
            case "EquationTerm":
            case "FunctionApplication":
            case "ParenTerm":
                return A
            
            case "QuantifierApplication": {
                let VL: VariableBinding[] = []
                for (let vb of A.vars) {
                    let MG = MGet(vb.symbol.ident)
                    if (MG) {
                        VL.push({
                            kind: "VariableBinding",
                            symbol: mk_var(MG),
                            type: vb.type
                        })
                    }
                }
                return {
                    kind: "QuantifierApplication",
                    term: A.term,
                    quantifier: A.quantifier,
                    vars: VL
                }
            }
            case "Variable": {
                let MG = MGet(A.ident)
                if (MG) return mk_var(MG)
                return A
            }

        }
    }
}
function replace_vars(M: Map<string, string>, unalpha: boolean = false): (x: Term) => Term {
    return stateless_map_terms(replace_var(M, unalpha))
}