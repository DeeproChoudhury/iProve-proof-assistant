export function rec_on(T: Type, type_def: TypeDef): (ident_: string, motive: Term) => Term {
    return (ident_: string, motive: Term): Term => {
        let ident: Variable = mk_var(ident_);

        let cases: Term[] = type_def.cases.map(con => {
            let vars: [Variable, Type][] = con.params.map(
                (v, i) => [mk_var(`InductiveParameter${i}`), v]
            );
            let subbed = strict_rw(motive, ident, construct_type(
                con,
                vars.map(x => x[0])
            ));

            let precons: Term[] = vars
                .filter(pt => pt[1] == T)
                .map(pt => strict_rw(motive, ident, pt[0]))
            let final_case: Term = imply(LI.conjunct(precons), subbed)
            
            return range_over(final_case, vars)
        })

        return imply(
            LI.conjunct(cases),
            range_over(motive, [[ident, T]]));
        }
}