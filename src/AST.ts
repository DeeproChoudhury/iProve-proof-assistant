export type ASTNode = { }

export type Symbol = ASTNode & {
    isSymbol: true,
    ident: String
}
export type Variable = Symbol & Term & { 
    isVariable: true
 }
export type Type = Symbol & { 
    isType: true
 }
export type FunctionSymbol = Symbol & { 
    isFunctionSymbol: true
 }
export type PredicateSymbol = Symbol & { 
    isPredicateSymbol: true
 }
export type RawSymbol = Variable & Type & FunctionSymbol & PredicateSymbol & { 
    isRawSymbol: true
 }
export type InfixFnSymbol = FunctionSymbol & {
    isInfixFnSymbol: true,
    infix: InfixSymbol
}
export type InfixSymbol = ASTNode & {
    isInfixSymbol: true,
    ident: String
}

export type FunctionType = ASTNode & {
    isFunctionType: true,
    A: Type,
    B: Type
}

export type Line = ASTNode & { }

export type TypeExt = Line & {
    isTypeExt: true,
    A: Type,
    B: Type
}

export type Declaration = Line & { 
    isDeclaration: true
}
export type FunctionDeclaration = Declaration & {
    isFunctionDeclaration: true,
    symbol: FunctionSymbol,
    type: FunctionType
}
export type VariableDeclaration = Declaration & {
    isVariableDeclaration: true,
    symbol: Variable,
    type: Type
}

export type Formula = Line & { 
    isFormula: true
}
export type PropLiteral = Formula & {
    isPropLiteral: true,
    truth: boolean,
 }

export type Neg = Formula & {
    isNeg: true,
    A: Formula
}
export type Bin = Formula & {
    isBin: true,
    A: Formula,
    B: Formula
}
export type And = Bin & {
    isAnd: true
}
export type Or = Bin & { 
    isOr: true
 }

export type VLElem = ASTNode & {
    isVLElem: true,
    v: Variable,
    T?: Type
}

export type Quantifier = Formula & {
    isQuantifier: true,
    vars: Array<VLElem>,
    A: Formula
}
export type UnivQuantifier = Quantifier & {
    isUnivQuantifier: true
 }
export type ExisQuantifier = Quantifier & {
    isExisQuantifier: true
 }

export type Imp = Formula & {
    isImp: true,
    A: Formula,
    B: Formula
}
export type Implies = Imp & {
    isImplies: true
 }
export type Iff = Imp & {
    isIff: true
}

export type Comparison = Formula & {
    isComparison: true,
    op: InfixSymbol,
    x: Term,
    y: Term,
}

export type Predicate = Formula & {
    isPredicate: true,
    pred: PredicateSymbol,
    terms: Array<Term>
}

export type Term = ASTNode & {
    isTerm: true
 }
export type Function = Term & {
    isFunction: true,
    fn: FunctionSymbol,
    terms: Array<Term>
}
export type IntLiteral = Term & {
    isIntLiteral: true,
    x: number
}
export type Infix = Term & {
    isInfix: true,
    x: Term,
    y: Term
}
export type InfixApplication = Infix & {
    isInfixApplication: true,
    fn: InfixSymbol
}
export type InfixFnApplication = Infix & {
    isInfixFnApplication: true,
    fn: FunctionSymbol
}
export type ArraySlice = Term & { 
    isArraySlice: true,
    ident: Variable
}
export type ArrayElem = ArraySlice & {
    isArrayElem: true,
    idx: Term
}
export type ArrayRange = ArraySlice & {
    isArrayRange: true,
    begin: Term,
    end: Term
}