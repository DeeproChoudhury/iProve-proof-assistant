import * as AST from "../types/AST";
import { IdentState } from "../types/LogicInterface";
import { conjunct, construct_type, display, imply, mk_var, range_over, strict_rw } from "../util/trees";
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
export function rec_on(T: AST.Type, type_def: AST.TypeDef):
    (ident_: string, motive: AST.Term) => AST.Term {
        return (ident_, motive) => 
            mutual_rec_on([T], [type_def])([ident_], [motive])
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
export function mutual_rec_on(Ts: AST.Type[], type_defs: AST.TypeDef[]):
 (idents_: string[], motives: AST.Term[]) => AST.Term {
    return (idents_: string[], motives: AST.Term[]): AST.Term => {
        console.log("HERE WE GO", idents_, motives, Ts, type_defs)
        let idents: AST.Variable[] = idents_.map(mk_var);
        let Tsd = Ts.map(display)
        let Tset = new Set(Tsd);

        let cum_precons: AST.Term[] = []
        for (let [i, type_def] of type_defs.entries()) {
            let motive = motives[i]
            let T = Ts[i]
            let ident = idents[i]

            let cases: AST.Term[] = type_def.cases.map(con => {
                let vars: [AST.Variable, AST.Type][] = con.params.map(
                    (v, j) => [mk_var(`InductiveParameter${j}`), v]
                );
                
                let subbed = strict_rw(motive, ident, construct_type(
                    con,
                    vars.map(x => x[0])
                ));

                let precons: AST.Term[] = vars
                    .filter(pt => Tset.has(display(pt[1])))
                    .map(pt => {
                        let idx = Tsd.indexOf(display(pt[1]))
                        return strict_rw(motives[idx], idents[idx], pt[0])
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
            range_over(full_motive, idents.map( (x, i) => [x, Ts[i]] ))
        );
    }
}


const TD1 = evaluate("type Reds ::= BaseR | Red Greens Int") as AST.TypeDef
const TD2 = evaluate("type Greens ::= BaseG | Green Reds") as AST.TypeDef
const M1 = evaluate("P(x)") as AST.Term
const M2 = evaluate("Q(x)") as AST.Term

console.log(display(mutual_rec_on(
    [{kind: "PrimitiveType", ident: "Reds"}],
    [TD1]
)(["x"], [M1])))