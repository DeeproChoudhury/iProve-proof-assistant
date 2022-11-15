export type ASTNode = Type | FunctionType | VariableBinding | Line | Pattern | Guard | TypeConstructor

export type TypeDef = {
    kind: "TypeDef",
    ident: string,
    params: string[],
    cases: TypeConstructor[]
}

export type TypeConstructor = {
    kind: "TypeConstructor",
    ident: string,
    params: Type[]
}

export type Tactic = Assumption | Skolemize | BeginScope | EndScope
export type Assumption = {
    kind: "Assumption",
    arg: Term
}
export type Skolemize = {
    kind: "Skolemize",
    arg: string
}
export type BeginScope = {
    kind: "BeginScope"
}
export type EndScope = {
    kind: "EndScope"
}

export type FunctionDefinition = {
    kind: "FunctionDefinition",
    ident: string,
    params: Pattern[],
    def: Guard | Term
}

export type Guard = {
    kind: "Guard",
    cond: Term,
    res: Term,
    next: Guard | undefined
}

export type Pattern = SimpleParam | ConsParam | EmptyList | ConstructedType | TuplePattern
export type SimpleParam = {
    kind: "SimpleParam",
    ident: string
}
export type ConsParam = {
    kind: "ConsParam",
    A: string,
    B: string
}
export type EmptyList = {
    kind: "EmptyList"
}
export type ConstructedType = {
    kind: "ConstructedType",
    c: string,
    params: Pattern[]
}
export type TuplePattern = {
    kind: "TuplePattern",
    params: Pattern[]
}

export type Type = PrimitiveType | ParamType | ListType | TupleType
export type PrimitiveType = { 
    kind: "PrimitiveType",
    ident: string
}
export type ParamType = { 
    kind: "ParamType",
    ident: string,
    params: Type[]
}
export type ListType = { 
    kind: "ListType",
    param: Type
}
export type TupleType = {
    kind: "TupleType",
    params: Type[]
}

export type FunctionType = {
    kind: "FunctionType",
    argTypes: Type[],
    retType: Type
}

export type VariableBinding = {
    kind: "VariableBinding",
    symbol: Variable,
    type?: Type
}

export type Line = TypeExt | Declaration | Term | Tactic | FunctionDefinition | TypeDef

export type TypeExt = {
    kind: "TypeExt",
    subType: Type,
    superType: Type
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

export type FunctionApplication = PrefixApplication | UnaryApplication | InfixApplication | ArrayElem | ArraySlice

export type AppType = FunctionApplication["appType"]

export type Variable = { 
    kind: "Variable",
    ident: string
}

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

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: VariableBinding[],
    quantifier: "E" | "A"
}

export type EquationTerm = {
    kind: "EquationTerm",
    lhs: Term,
    rhs: Term
}

export type ParenTerm = { 
    kind: "ParenTerm",
    term: Term
}

function fnDisplay(fn: string): string {
    switch (fn) {
        case "~": return "¬"; 
        case "&": return "∧";
        case "|": return "∨";
        case "^": return "⊕";
        case "->": return "→";
        case "<->": return "↔";
        default: return fn;
    }
}

function fnSMT(fn: string): string {
    switch (fn) {
        case "~": return "not";
        case "&": return "and";
        case "|": return "or";
        case "^": return "xor";
        case "->": return "implies";
        case "<->": return "=";
        default: return fn;
    }
}

function d(a: ASTNode): string {
    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(d).join(", ")}) -> ${d(a.retType)}`;
        case "TypeExt": return `${d(a.subType)} ⊆ ${d(a.superType)}`;
        case "VariableBinding": return s(a.symbol) + (a.type ? `: ${d(a.type)}` : "");
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
    }
}


export const display: (line: Line) => string = d


export function s(a: ASTNode | undefined) : string {
    if(a === undefined) {
        return "NULL";
    }

    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(s).join(" ")})  ${s(a.retType)}`;
        case "VariableBinding": return `(${s(a.symbol)} ${a.type ? s(a.type) : "Int"})`;
        case "TypeExt": return `${s(a.subType)} ⊆ ${s(a.superType)}`;
        case "FunctionDeclaration": return `(declare-fun ${a.symbol} ${s(a.type)})`;
        case "VariableDeclaration": return `(declare-const ${s(a.symbol)} ${a.type ? `${s(a.type)}` : "Int"})`;
        case "Variable": return a.ident;
        case "FunctionApplication": return `(${fnSMT(a.fn)} ${a.params.map(s).join(" ")})`;
        case "QuantifierApplication": return `(${a.quantifier === "E" ? "exists" : "forall"} (${a.vars.map(s).join(" ")}) ${s(a.term)})`;
        case "EquationTerm": return `${s(a.lhs)} ::= ${s(a.rhs)}`;
        case "ParenTerm": return s(a.term);

        case "BeginScope":
        case "EndScope":
        case "Assumption":
        case "Skolemize":
            return "";

        case "FunctionDefinition":
        case "Guard":
        case "SimpleParam":
        case "ConsParam":
        case "EmptyList":
        case "ConstructedType":
        case "TuplePattern":
            return ""
        
        case "TypeDef":
        case "TypeConstructor":
            return "";

        case "ParamType":
        case "ListType":
        case "TupleType":
            return "";
    }
}

export const ASTSMTLIB2: (line: Line | undefined) => string = s;
