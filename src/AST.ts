export type ASTNode = Type | FunctionType | Line

export type Type = { 
    kind: "Type",
    ident: string
}

export type FunctionType = {
    kind: "FunctionType",
    A: Type[],
    B: Type
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

export type Term = Variable | FunctionApplication | QuantifierApplication | EquationTerm | ParenTerm

export type FunctionApplication = UnaryApplication | PrefixApplication | InfixApplication | ArrayElem | ArraySlice

export type AppType = FunctionApplication["appType"]

export type PrefixApplication = {
    kind: "FunctionApplication",
    appType: "PrefixFunc" | "PrefixOp",
    fn: string,
    params: Term[]
}

export type UnaryApplication = {
    kind: "FunctionApplication",
    appType: "UnaryFunc" | "UnaryOp",
    fn: string,
    params: [Term]
}

export type InfixApplication = {
    kind: "FunctionApplication",
    appType: "InfixFunc" | "InfixOp",
    fn: string,
    params: [Term, Term]
}

export type ArrayElem = {
    kind: "FunctionApplication",
    appType: "ArrayElem",
    fn: "select",
    params: [Term, Term]
}

export type ArraySlice = {
    kind: "FunctionApplication",
    appType: "ArraySlice",
    fn: "???", // TODO
    params: [Term, Term?, Term?]
}

export type Variable = { 
    kind: "Variable",
    ident: string
}

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: VariableDeclaration[],
    quantifier: "E" | "A"
}

export type EquationTerm = {
    kind: "EquationTerm",
    lhs: Term,
    rhs: Term
}

export type ParenTerm = { 
    kind: "ParenTerm",
    x: Term
}

function d(a: ASTNode): string {
    switch (a.kind) {
        case "Type": return a.ident;
        case "FunctionType": return `(${a.A.map(d).join(", ")}) -> ${d(a.B)}`;
        case "TypeExt": return `${d(a.A)} ⊆ ${d(a.B)}`;
        case "FunctionDeclaration": return `${a.symbol} :: ${d(a.type)}`;
        case "VariableDeclaration": return `var ${d(a.symbol)}` + (a.type ? `: ${d(a.type)}` : "");
        case "Variable": return a.ident;
        case "FunctionApplication": switch (a.appType) {
            case "PrefixFunc": return `${a.fn}(${a.params.map(d).join(", ")})`;
            case "PrefixOp": return `(${a.fn})(${a.params.map(d).join(", ")})`;
            case "InfixFunc": return `${d(a.params[0])} \`${a.fn}\` ${d(a.params[1])}`;
            case "InfixOp": return `${d(a.params[0])} ${a.fn} ${d(a.params[1])}`;
            case "UnaryFunc": return `$\`${a.fn}\` ${d(a.params[0])}`;
            case "UnaryOp": return `${a.fn} ${d(a.params[0])}`;
            case "ArrayElem": return `${d(a.params[0])}[${d(a.params[1])}]`;
            case "ArraySlice": return `${d(a.params[0])}[${(a.params[1]) ? d(a.params[1]) : ""}..${(a.params[2]) ? d(a.params[2]) : ""})`;
        }
        case "QuantifierApplication": return `${a.quantifier === "E" ? "∃" : "∀"}(${a.vars.map(d).join(",")}).${d(a.term)}`;
        case "EquationTerm": return `${d(a.lhs)} ::= ${d(a.rhs)}`;
        case "ParenTerm": return `[${d(a.x)}]`;
    }
}

export const display = d
