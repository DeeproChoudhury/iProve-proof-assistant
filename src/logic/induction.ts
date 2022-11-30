import * as AST from "../types/AST";
import { conjunct, construct_type, display, imply, mk_var, range_over, strict_rw } from "../util/trees";

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
export function rec_on(T: AST.Type, type_def: AST.TypeDef): (ident_: string, motive: AST.Term) => AST.Term {
    return (ident_: string, motive: AST.Term): AST.Term => {
        let ident: AST.Variable = mk_var(ident_);

        let cases: AST.Term[] = type_def.cases.map(con => {
            let vars: [AST.Variable, AST.Type][] = con.params.map(
                (v, i) => [mk_var(`InductiveParameter${i}`), v]
            );
            let subbed = strict_rw(motive, ident, construct_type(
                con,
                vars.map(x => x[0])
            ));

            let precons: AST.Term[] = vars
                .filter(pt => display(pt[1]) == display(T))
                .map(pt => strict_rw(motive, ident, pt[0]))
            let final_case: AST.Term = imply(conjunct(precons), subbed)
            
            return range_over(final_case, vars)
        })

        return imply(
            conjunct(cases),
            range_over(motive, [[ident, T]]));
        }
}