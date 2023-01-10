export type ASTNode = Type | FunctionType | VariableBinding | Line | Pattern | TypeConstructor | Guard

export type TypeDef = {
    kind: "TypeDef",
    ident: string,
    params: string[],
    cases: TypeConstructor[]
}

export type TypeConstructor = {
    kind: "TypeConstructor",
    ident: string,
    params: Type[],
    selectors: string[]
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
    A: Pattern,
    B: Pattern
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
    tag?: "Set" | "Predicate" | "Relation"
}

export type VariableBinding = {
    kind: "VariableBinding",
    symbol: Variable,
    type?: Type,
    bound?: number,
    boundType?: ">=" | "<=" | ">" | "<"
}
export type BlockStart = VariableDeclaration | Assumption | BeginScope;
export type Line = Declaration | Term | Tactic | FunctionDefinition | TypeDef

export type Declaration = FunctionDeclaration | VariableDeclaration | SortDeclaration

export type FunctionDeclaration = {
    kind: "FunctionDeclaration",
    symbol: string,
    type: FunctionType,
    partial: boolean
}

export type VariableDeclaration = {
    kind: "VariableDeclaration",
    symbol: Variable,
    type?: Type
}

export type SortDeclaration = {
    kind: "SortDeclaration",
    symbol: Variable,
    arity: number
}

export type Term = Variable | FunctionApplication | QuantifierApplication | EquationTerm | ParenTerm | ArrayLiteral

export type FunctionApplication = PrefixApplication | UnaryApplication | InfixApplication | ArrayElem | ArraySlice

export type AppType = FunctionApplication["appType"]

export type Variable = { 
    kind: "Variable",
    ident: string
}

export type ArrayLiteral = {
    kind: "ArrayLiteral",
    elems: Term[],
    type?: Type
}

export type PrefixApplication = {
    kind: "FunctionApplication",
    appType: "PrefixFunc" | "PrefixOp",
    typeParams?: Type[],
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
    fn: "ArraySelect",
    params: [Term, Term]
}

export type ArraySlice = {
    kind: "FunctionApplication",
    appType: "ArraySlice",
    fn: "ArraySlice", // TODO
    params: [Term, Term] | [Term, Term, Term]
}

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: VariableBinding[],
    quantifier: "E" | "A",

    var_nesting?: number[]
}

export type EquationTerm = {
    kind: "EquationTerm",
    lhs: Term,
    rhs: Term
}

export type ParenTerm = { 
    kind: "ParenTerm",
    term: Term,
    isSquare: boolean
}



