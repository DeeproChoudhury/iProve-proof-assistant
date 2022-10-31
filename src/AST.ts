export type ASTNode = Type | FunctionType | SortedVariable | Line

 export type Variable = { 
    kind: "Variable",
    ident: String
 }

export type Type = { 
    kind: "Type",
    ident: String
 }

 export type FunctionType = {
    kind: "FunctionType",
    A: Type,
    B: Type
}

export type FunctionApplication = PrefixApplication | InfixApplication | ArrayElem | ArraySlice

export type AppType = FunctionApplication["appType"]

export type PrefixApplication = {
    kind: "PrefixApplication",
    appType: "PrefixFunc" | "PrefixOp",
    fn: string,
    params: Term[]
}

export type InfixApplication = {
    kind: "InfixApplication",
    appType: "InfixFunc" | "InfixOp",
    fn: string,
    params: [Term, Term]
}

export type ArrayElem = {
    kind: "ArrayElem",
    appType: "ArrayElem",
    fn: "select",
    params: [Term, Term]
}

export type ArraySlice = {
    kind: "ArraySlice",
    appType: "ArraySlice",
    fn: "???",
    params: [Term, Term, Term]
}

export type Line = TypeExt | Declaration | Term

export type TypeExt = {
    kind: "TypeExt",
    A: Type,
    B: Type
}

export type Declaration = FunctionDeclaration | VariableDeclaration

export type FunctionDeclaration = {
    kind: "FunctionDeclaration",
    symbol: string,
    type: FunctionType
}

export type VariableDeclaration = {
    kind: "VariableDeclaration",
    symbol: Variable,
    type?: Type
}

export type SortedVariable = {
    kind: "SortedVariable",
    symbol: Variable,
    type?: Type
}

export type Term = FunctionApplication | QuantifierApplication | Variable | EquationTerm | ParenTerm

export type ParenTerm = { 
    kind: "ParenTerm",
    x: Term
}

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: [SortedVariable],
    quantifier: "E" | "A"
}

export type EquationTerm = {
    kind: "EquationTerm",
    lhs: Term,
    rhs: Term
}




function interleave<T>(a: T[], b: T[]): T[] {
    const c = [];
    let i;
    for (i = 0; i < a.length && i < b.length; i++) {
        c.push(a[i]);
        c.push(b[i]);
    }
    if (i < a.length) c.push(a[i]);
    return c;
}

export function display(a: ASTNode): string {
    switch (a.kind) {
        case "Variable":
        case "FunctionSymbol":
        case "PredicateSymbol":
        case "Type": 
        case "InfixSymbol":
            return `${a.ident}`;
        case "PropOperator":
        case "ImpOperator":
            return `${a.op}`;
        case "FunctionType": return `${display(a.A)} -> ${display(a.B)}`;
        case "TypeExt": return `${display(a.A)} ⊆ ${display(a.B)}`;
        case "FunctionDeclaration": return `${display(a.symbol)} :: ${display(a.type)}`;
        case "VariableDeclaration": return `var ${a.symbol}` + (a.type ? `: ${display(a.type)}` : "");
        case "SortedVariable": return a.T ? `(${display(a.v)} : ${display(a.T)})` : `(${display(a.v)})`;
        case "Term": return `${interleave(a.atoms.map(display), a.operators.map(display)).join(" ")}`;
        case "Function": return `${display(a.fn)}(${a.terms.map(display).join(", ")})`;
        case "IntLiteral": return a.n.toString();
        case "ArrayElem": return `${display(a.ident)}[${display(a.idx)}]`;
        case "ArrayRange": return `${display(a.ident)}[${display(a.begin)}..${display(a.end)})`;
        case "ParenTerm": return `(${display(a.x)})`;
        case "Neg": return `¬${display(a.A)}`;
        case "PropLiteral": return a.truth ? "⊤" : "⊥";
        case "Comparison": return `${display(a.x)} ${display(a.op)} ${display(a.y)}`;
        case "Predicate": return `${display(a.pred)}(${a.terms.map(display).join(", ")})`;
        case "QFClause": return `${interleave(a.atoms.map(display), a.operators.map(display)).join(" ")}`;
        case "QuantifiedFormula": return `${a.quantifier === Quantifier.E ? "∃" : "∀"}${a.vars.map(display).join("")}.${display(a.A)}`;
        case "Formula": return `${interleave(a.clauses.map(display), a.operators.map(display)).join(" ")}`;
        case "ParenFormula": return `(${display(a.A)})`;
    }
}
