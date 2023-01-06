import * as AST from "../types/AST"
import { AlphaAssignment, Unification, UnifyFail, UnifyScope } from "../types/LogicInterface"
import { display, iff, isDeclaration, mk_var, ParamType, PrimitiveType } from "../util/trees"
import { LogicInterface } from "./LogicInterface"
import { LIQ } from "./LogicInterfaceQueue"
import evaluate from "./Parser"
import { basic_preprocess, CommOperators, replace_vars, unify_preprocess } from "./simplifiers"
import { bitmap_mex, get_from_scope, pop_scope, push_scope, set_bit, set_in_scope } from "./util"

export const UNIFY_FAIL: UnifyFail = { kind: "UnifyFail" }

function gen_unify_poss(
    i: number,
    A: AST.Term[],
    B: AST.Term[],
    bitmap: number,
    scope: UnifyScope): Unification 
{
    console.log("ANAB", A, B)
    if (i >= A.length) return scope

    let b_i: number | undefined = -1
    while (true) {
        b_i = bitmap_mex(bitmap, b_i + 1)
        if (b_i >= B.length) return UNIFY_FAIL

        push_scope(scope)
        if (gen_unify(A[i], B[b_i], scope).kind == "UnifyScope") {
            let res = gen_unify_poss(i + 1, A, B, set_bit(bitmap, b_i), scope)
            if (res.kind == "UnifyScope") return scope
        }
        pop_scope(scope)
    }
}

export function gen_decls(T: AST.TypeDef): [AST.SortDeclaration[], AST.FunctionDeclaration[]] {
    console.log("HERE IS GEN_DECLS")
    let R1: AST.SortDeclaration[] = [{
         kind: "SortDeclaration", symbol: mk_var(T.ident), arity: T.params.length }
        ];
    for (let param of T.params) R1.push(
        { kind: "SortDeclaration", symbol: mk_var(param), arity: 0 }
    );
    let R2: AST.FunctionDeclaration[] = [];
    for (let cons of T.cases) {
        R2.push({
            kind: "FunctionDeclaration",
            symbol: cons.ident,
            type: {
                kind: "FunctionType",
                retType: T.params.length > 0
                    ? ParamType(T.ident, T.params.map(PrimitiveType))
                    : PrimitiveType(T.ident),
                argTypes: cons.params,
            }
        });
    }
    console.log(R1, R2)
    return [R1, R2];
}

/**
 * The recursive driver function around which `unifies` is a wrapper.
 * 
 * @remarks
 * 
 * This process uses recursion with backtracking to attempt to find a satisfying
 * alpha-assignment, and on failure will reorder any conjunctions. This
 * is factorial in the number of nested commutative operations.
 * 
 * @param A - The first term
 * @param B - The second term
 * @param scope - The scope containing current assignments and sorts
 * @returns Either an unpdated assignment, or a UnifyFail
 * 
 */
function gen_unify(A: AST.Term | undefined, B: AST.Term | undefined, scope: UnifyScope): Unification {
    if (!A || !B) {
        return ((!A) && (!B))
            ? scope : UNIFY_FAIL
    }

    switch (A.kind) {
        case "ArrayLiteral": {
            if (B.kind != "ArrayLiteral"
                || A.elems.length != B.elems.length) return UNIFY_FAIL
            
            let c_v: Unification = scope;
            for (let i = 0; i < A.elems.length; i++) {
                c_v = gen_unify(A.elems[i], B.elems[i], c_v)
                if (c_v.kind == "UnifyFail") return UNIFY_FAIL
            }
            return c_v;
        }
        case "EquationTerm": {
            if (B.kind != "EquationTerm") return UNIFY_FAIL
            let lhs_verdict = gen_unify(A.lhs, B.lhs, scope)
            let rhs_verdict = gen_unify(A.rhs, B.rhs, scope)
            if (rhs_verdict.kind == "UnifyFail" || lhs_verdict.kind == "UnifyFail")
                return UNIFY_FAIL

            return scope
        }
        case "ParenTerm": {
            if (B.kind != "ParenTerm") return UNIFY_FAIL
            return gen_unify(A.term, B.term, scope)
        }
        case "Variable": {
            if (B.kind != "Variable") return UNIFY_FAIL
            console.log("[at variable]", A.ident, B.ident)

            if (!scope.sort_ctx_a.has(A.ident) || 
                !scope.sort_ctx_b.has(B.ident) )
                return (A.ident == B.ident) ? scope : UNIFY_FAIL

            if (!get_from_scope(scope, A.ident)) {
                let set_verdict = set_in_scope(scope, A.ident, B.ident);
                if (!set_verdict) return UNIFY_FAIL
            }

            return (get_from_scope(scope, A.ident) == B.ident)
                ? scope
                : UNIFY_FAIL
        }
        case "QuantifierApplication": {
            if (B.kind != "QuantifierApplication"
                || B.quantifier != A.quantifier
                || B.vars.length != A.vars.length)
                return UNIFY_FAIL

            let type_cnts: Map<string, number> = new Map
            let d_ = (x: AST.Type | undefined): string => {
                if (!x) return "any"
                return display(x)
            }
            for (let i = 0; i < A.vars.length; i++) {
                scope.sort_ctx_a.set(A.vars[i].symbol.ident, d_(A.vars[i].type))
                scope.sort_ctx_b.set(B.vars[i].symbol.ident, d_(B.vars[i].type))
                
                let tca: number | undefined = type_cnts.get(d_(A.vars[i].type))
                if (!tca) tca = 0
                type_cnts.set(d_(A.vars[i].type), tca + 1)
                let tcb: number | undefined = type_cnts.get(d_(B.vars[i].type))
                if (!tcb) tcb = 0
                type_cnts.set(d_(B.vars[i].type), tcb - 1)
            }

            //console.log(type_cnts)
            for (let [_,v] of type_cnts)
                if (v != 0) return UNIFY_FAIL

            return gen_unify(A.term, B.term, scope)
            
        }
        case "FunctionApplication": {
            let N = A.params.length
            if (B.kind != "FunctionApplication"
                || N != B.params.length
                || A.fn != B.fn) return UNIFY_FAIL
            
            if (!CommOperators.has(A.fn)) {
                for (let i = 0; i < A.params.length; i++) {
                    let c_v = gen_unify(A.params[i], B.params[i], scope)
                    if (c_v.kind == "UnifyFail") return UNIFY_FAIL
                }
                return scope
            }

            // repeating A/B cases to allow non-matching appTypes
            // in terms of prefix/infix
            if (A.appType == "ArrayElem"
                || A.appType == "ArraySlice"
                || A.appType == "UnaryFunc"
                || A.appType == "UnaryOp"
                || B.appType == "ArrayElem"
                || B.appType == "ArraySlice"
                || B.appType == "UnaryFunc"
                || B.appType == "UnaryOp")
                return UNIFY_FAIL
            
            return gen_unify_poss(0, A.params, B.params, 0, scope)
        }
    }
}

/**
 * Given terms A,B, attempts to generate an alpha-equivalence between them,
 * applying axioms of associativity and commutativity of operators if
 * needed.
 * 
 * @remarks
 * 
 * We call this process of alpha-equivalence finding *unification*, as we
 * are specifically employing the axioms that
 *   - `AND, OR` are commutative
 *   - `AND, OR` are associative
 * Hence given the terms `A & [B & A]` and `[X & X] & Y`, the equivalence X => A,
 * Y => B will be found even though these are not structurally equal terms.
 * 
 * @param A_ - The first term (whose variables will be the keys of the mapping)
 * @param B_ - The second term (whose variables will be the values of the mapping)
 * @returns Either a satisfying assignment, or undefined if there is none
 * 
 */
export function unifies(A_: AST.Term, B_: AST.Term): AlphaAssignment | undefined {
    let A: AST.Term = unify_preprocess(A_)
    let B: AST.Term = unify_preprocess(B_)

    console.log("HERE AB")
    console.log(display(A))
    console.log(display(B))

    let verdict: Unification = gen_unify(B, A, {
        kind: "UnifyScope",
        sort_ctx_a: new Map,
        sort_ctx_b: new Map,
        assignments: [new Map]
    })

    return (verdict.kind == "UnifyFail")
    ? undefined
    : { kind: "AlphaAssignment",
        term: replace_vars(verdict.assignments.reduce((x, y) => {
            return new Map([...y,...x])
        }, new Map()))(basic_preprocess(B_)),
        assn: verdict.assignments.reduce((x, y) => {
            return new Map([...y,...x])
        }, new Map()) }
}