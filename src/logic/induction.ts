import * as AST from "../types/AST";
import { IdentState } from "../types/LogicInterface";
import { conjunct, construct_type, display, imply, mk_var, range_over, strict_rw, substitute_types } from "../util/trees";
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
            let BIT = bindings[i].type

            if (!BIT || BIT.kind == "ListType" || BIT.kind == "TupleType") { 
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

            let ident = bindings[i].symbol;
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
            range_over(full_motive, bindings.map((x) => [x.symbol, x.type as AST.Type]))
        );
    }
}