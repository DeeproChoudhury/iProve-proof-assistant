function d(a: ASTNode): string {
    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(d).join(", ")}) -> ${d(a.retType)}`;
        case "TypeExt": return `${d(a.subType)} ⊆ ${d(a.superType)}`;
        case "VariableBinding": return d(a.symbol) + (a.type ? `: ${d(a.type)}` : "");
        case "FunctionDeclaration": return `${a.symbol} :: ${d(a.type)}`;
        case "VariableDeclaration": return `var ${d(a.symbol)}` + (a.type ? `: ${d(a.type)}` : "");
        case "Variable": return a.ident;
        case "FunctionApplication": {
            const fn = fnDisplay(a.fn);
            switch (a.appType) {
                case "PrefixFunc": return `${fn}(${a.params.map(d).join(", ")})`;
                case "PrefixOp": return `(${fn})(${a.params.map(d).join(", ")})`;
                case "InfixFunc": return `${d(a.params[0])} \`${fn}\` ${d(a.params[1])}`;
                case "InfixOp": return `${d(a.params[0])} ${fn} ${d(a.params[1])}`;
                case "UnaryFunc": return `$\`${fn}\` ${d(a.params[0])}`;
                case "UnaryOp": return `${fn} ${d(a.params[0])}`;
                case "ArrayElem": return `${d(a.params[0])}[${d(a.params[1])}]`;
                case "ArraySlice": {
                    const p1 = (a.params[1]) ? d(a.params[1]) : "";
                    const p2 = (a.params[2]) ? d(a.params[2]) : "";
                    return `${d(a.params[0])}[${p1}..${p2})`;
                }
            }
        }
        case "QuantifierApplication": return `${a.quantifier === "E" ? "∃" : "∀"}(${a.vars.map(d).join(",")}).${d(a.term)}`;
        case "EquationTerm": return `${d(a.lhs)} ::= ${d(a.rhs)}`;
        case "ParenTerm": return `[${d(a.term)}]`;
        
        case "BeginScope": return "begin";
        case "EndScope": return "end";
        case "Assumption": return `assume ${d(a.arg)}`;
        case "Skolemize": return `skolem ${a.arg}`;

        case "FunctionDefinition":
            return `${a.ident} ${a.params.map(d).join(" ")} ::= ${d(a.def)}` 
        case "Guard": return `\n  | ${a.cond} := ${a.res}`
        case "SimpleParam": return `${a.ident}`
        case "ConsParam": return `(${a.A}::${a.B})`
        case "EmptyList": return "[]"
        case "ConstructedType": 
            return `(${a.c} ${a.params.map(d).join(" ")})` 
        case "TuplePattern":
            return `(${a.params.map(d).join(", ")})` 
        
        case "TypeDef": return `type ${a.ident} ::= ${a.cases.map(d).join(" | ")}`
        case "TypeConstructor": return `${a.ident} ${a.params.map(d).join(" ")}` 

        case "ParamType": return `${a.ident}<${a.params.map(d).join(",")}>`
        case "ListType": return `[${d(a.param)}]`
        case "TupleType": return `(${a.params.map(d).join(", ")})`

        case "ArrayLiteral": return `{ ${a.elems.map(d).join(", ")} }`
    }
}
export const display: (line: Line) => string = d

export const isTerm = (line: Line): line is Term => (
    line.kind === "Variable"
        || line.kind === "FunctionApplication"
        || line.kind === "QuantifierApplication"
        || line.kind === "EquationTerm"
        || line.kind === "ParenTerm"
)

export function construct_type(con: TypeConstructor, params: Variable[]): PrefixApplication {
    return {
        kind: "FunctionApplication",
        appType: "PrefixFunc",
        fn: con.ident,
        params: params
    }
}

export function mk_var(ident: string): Variable {
    return {
        kind: "Variable",
        ident: ident
    }
}

export function range_over(t: Term, vars: [Variable, Type][]): Term {
    return vars.length ?
    {
        kind: "QuantifierApplication",
        term: parenthesize(t),
        vars: vars.map((v: [Variable, Type]) => ({
            kind: "VariableBinding",
            symbol: v[0],
            type: v[1]
        })),
        quantifier: "A"
    }
    : t
}

export function imply(L: Term | undefined, R: Term): Term {
    if (!L) return R;
    return {
        kind: "FunctionApplication",
        appType: "InfixOp",
        fn: "->",
        params: [parenthesize(L), parenthesize(R)]
    }
}

export function parenthesize(t: Term): ParenTerm {
    return {
        kind: "ParenTerm",
        term: t
    }
}

// NOTE: For obvious reasons, this will not rewrite in itself. 
export function strict_rw(goal: Term, L: Term, R: Term): Term {
    let f = (x: Term): Term => {
        let term_equal: Boolean = JSON.stringify(L) == JSON.stringify(x);
        return term_equal ? R : x
    }
    return stateless_map_terms(f)(goal);
}

export function seek_parens(A: Term): Term {
    let c_t: Term = A;
    while (c_t.kind == "ParenTerm") c_t = c_t.term
    return c_t
}