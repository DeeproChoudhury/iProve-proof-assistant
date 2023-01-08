import { render } from "@testing-library/react";
import * as AST from "../types/AST";
import { IdentState, PatternData } from "../types/LogicInterface";
import { conjunct, construct_type, display, imply, mk_var, PrimitiveType, range_over, range_over_bindings, strict_rw, substitute_types } from "../util/trees";
import { map_terms } from "./combinator";
import { LI, renderNode, renderPattern } from "./LogicInterface";
import evaluate from "./Parser";

/**
 * Given an inductively defined datatype, this combinator will return the *recursor map* of
 * the datatype, i.e. a function which, given an induction motive to be
 * proven for all instances of this type (where the variable being ranged
 * over is given as a parameter), it will return the induction principle
 * which implies the motive
 * 
 * @param T        - The type to be mapped
 * @param type_def - Its inductive definition
 * @returns The recursor map of T
 * 
 */
export function rec_on(type_def: AST.TypeDef):
    (binding: AST.VariableBinding, motive: AST.Term) => AST.Term {
        return (binding, motive) => 
            mutual_rec_on([type_def])([binding], [motive])
    }

/**
 * Given a list of datatypes and a list of type definitions, returns the *mutual
 * recursor map* of the datatypes. I.e. a function which, given a list of motives to be
 * proven for all instances of each respective type (where the variable being ranged
 * over is given as a parameter), it will return the induction principle
 * which implies the *conjunction of* the motives.
 * 
 * @remarks
 * 
 * The principal way in which this differs from independent solving of motives
 * is the ability to use *all* motives in the induction hypothesis. For
 * coupled mutually inductive types, this can be a great benefit
 * 
 * @param Ts        - The types to be mapped
 * @param type_defs - Their inductive definitions
 * @returns The mutual recursor map of Ts
 * 
 */
export function mutual_rec_on(type_defs: AST.TypeDef[]):
 (bindings: AST.VariableBinding[], motives: AST.Term[]) => AST.Term {
    let TMap = new Map(type_defs.map((x) => [x.ident, x]))
    return (bindings: AST.VariableBinding[], motives: AST.Term[]): AST.Term => {
        console.log("HERE WE GO", motives, type_defs)
        // :/
        for (let x of bindings) { if (!x.type) return { kind: "Variable", ident: "ERRORVAR"}; }
        let fts = bindings.map((x) => display(x.type as AST.Type))

        let cum_precons: AST.Term[] = []
        for (let [i, motive] of motives.entries()) {
            const BIT = bindings[i].type
            const ident = bindings[i].symbol;

            if (!BIT) { 
                cum_precons.push(range_over_bindings(motive, [bindings[i]])); continue;
            } 

            if (BIT.kind == "PrimitiveType" && BIT.ident == "Int") {
                const bound = bindings[i].bound;
                if (!bound) {
                    cum_precons.push(range_over_bindings(motive, [bindings[i]])); continue;
                }
                cum_precons.push(strict_rw(motive, ident, mk_var(`${bound}`)))

                let ivar = mk_var(`InductiveParameter${0}`)
                let precon = strict_rw(motive, ident, ivar)
                let subbed = strict_rw(motive, ident, {
                    kind: "FunctionApplication",
                    appType: "InfixOp",
                    fn: "+",
                    params: [ivar, mk_var("1")]
                });
                let final_case: AST.Term = imply(precon, subbed)
                cum_precons.push(range_over_bindings(final_case, [{
                    kind: "VariableBinding",
                    symbol: ivar,
                    type: BIT,
                    bound: bound
                }]))
                continue;
            }

            if (BIT.kind == "ListType" || BIT.kind == "TupleType") { 
                cum_precons.push(motive); continue;
            }
            let type_def = TMap.get(BIT.ident);
            if (!type_def) { 
                cum_precons.push(motive); continue;
            }
            console.log("AB", BIT.kind, type_def)
            if (BIT.kind == "ParamType")
                type_def = substitute_types(type_def, BIT.params);
            console.log("CD", BIT.kind, type_def)
            
            let cases: AST.Term[] = type_def.cases.map(con => {
                let vars: [AST.Variable, AST.Type][] = con.params.map(
                    (v, j) => { console.log(v.kind); return [mk_var(`InductiveParameter${j}`), v] }
                );

                console.log("VARS", `${type_def}`, vars.map((v) => display(v[1])))
                
                let subbed = strict_rw(motive, ident, construct_type(
                    con,
                    vars.map(x => x[0])
                ));

                let precons: AST.Term[] = vars
                    .flatMap(pt => {
                        let R = []
                        for (let [j, b] of fts.entries()) {
                            if (b == display(pt[1])) {
                                R.push(strict_rw(motives[j], bindings[j].symbol, pt[0]))
                            }
                        } 
                        return R
                    });
                let final_case: AST.Term = imply(conjunct(precons), subbed)
                return range_over(final_case, vars)
            })
            cum_precons = cum_precons.concat(cases)
        }

        console.log(cum_precons.map(display))
        let full_motive = conjunct(motives)
        if (!full_motive) return { kind: "Variable", ident: "ERRORVAR"};

        return imply(
            conjunct(cum_precons),
            range_over_bindings(full_motive, bindings)
        );
    }
}

function extract_call(id: string)
    : (T: AST.Term, state: AST.FunctionApplication[]) => [AST.Term, AST.FunctionApplication[]] {
        return (T: AST.Term, state: AST.FunctionApplication[]): [AST.Term, AST.FunctionApplication[]] => {
            if (T.kind == "FunctionApplication" && T.fn == id)
                state.push(T)
            return [T, state]
        }
}
export function extract_calls(id: string)
    : (T: AST.Term, state: AST.FunctionApplication[]) => [AST.Term, AST.FunctionApplication[]] {
        return map_terms(extract_call(id), [])
}

export function function_IP(decl: AST.FunctionDeclaration, defns: AST.FunctionDefinition[]):
    (to_sub: AST.FunctionApplication, vname: string, motive: AST.Term) => AST.Term {
        return (to_sub: AST.FunctionApplication, vname: string, motive: AST.Term): AST.Term => {
            if (!defns.length) return motive;

            // for each definition, extract the pattern condition/binding list
            let pdatas: [PatternData, AST.Term | AST.Guard][] = [];
            for (let a of defns) {
                let concu: PatternData = [];
                for (let [i,p] of a.params.entries()) {
                    //concu = concu.concat(renderPattern(p, `IProveParameter${i}`,))
                }
                pdatas.push([concu, a.def]);
            }

            // for each definition, extract the conditions and respective outcomes
            let conditions = []
            for (let [i, [p, d]] of pdatas.entries()) {
                let R = "true";
                for (let D of p.reverse()) {
                    if (D.kind == "Condition")
                        R = `(and ${R} ${D.value})`
                    else
                        R = `(let (${D.value}) ${R})`
                }

                let localConditions
                : {fst:string,rest:[AST.Term | undefined,AST.Term][]} 
                = { fst: R, rest: [] }

                if (d.kind == "Guard") {
                    localConditions.rest.push([d.cond, d.res])
                    let cd = d.next;
                    while (cd) {
                        localConditions.rest.push([cd.cond, cd.res])
                        cd = cd.next;
                    }
                } else {
                    localConditions.rest.push([undefined, d])
                }
                
                conditions.push(localConditions)
            }
            // for each possible outcome, extract all its preconditions
            // (exclusion -> pattern -> guard -> definedness)
            let outcomes: [string, AST.Term][] = []
            let cum_conditions: string = "true"
            for (let {fst, rest} of conditions) {
                for (let [c,v] of rest) {
                    let st = (!c)
                        ? `(and ${fst} ${cum_conditions})`
                        : `(and ${renderNode(c)} (and ${fst} ${cum_conditions}))`
                    st = `(and ${st} ${renderNode(LI.wellDef(v))})`
                    outcomes.push([st, v])
                    cum_conditions = (!c)
                        ? cum_conditions
                        : `(and ${cum_conditions} (not ${renderNode(c)}))`
                }
                cum_conditions = `(and ${cum_conditions} (not ${fst}))`
            }

            // iterate over the motive. We want to prove it for all outcomes,
            // so we prove that, for each possible outcome:
            //     - its preconditions being met
            //     - AND for every recursive call in its outcome, the motive holds
            //     - TOGETHER IMPLY the motive holds on the outcome
            let cases: AST.Term[] = []
            let extract_recursive = extract_calls(decl.symbol)
            for (let [cond, outcome] of outcomes) {
                let rec_calls: AST.FunctionApplication[] = extract_recursive(outcome, [])[1];
                let full_cond = `(and ${cond} )`
            }


            return mk_var("NOTIMPLEMENTEDVAR")
        }

        
}