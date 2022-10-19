export type ASTNode = { }

export type Symbol = ASTNode & {
    ident: String
}
export type Variable = Symbol & Term & {  }
export type Type = Symbol & {  }
export type FunctionSymbol = Symbol & {  }
export type PredicateSymbol = Symbol & {  }
export type RawSymbol = Variable & Type & FunctionSymbol & PredicateSymbol & { }
export type InfixFnSymbol = FunctionSymbol & {
    infix: InfixSymbol
}
export type InfixSymbol = ASTNode & {
    ident: String
}

export type FunctionType = ASTNode & {
    A: Type,
    B: Type
}

export type Line = ASTNode & { }

export type TypeExt = Line & {
    A: Type,
    B: Type
}

export type Declaration = Line & { }
export type FunctionDeclaration = Declaration & {
    symbol: FunctionSymbol,
    type: FunctionType
}
export type VariableDeclaration = Declaration & {
    symbol: Variable,
    type: Type
}

export type Formula = Line & { }
export type PropLiteral = Formula & {
    truth: boolean,
 }

export type Neg = Formula & {
    A: Formula
}
export type Bin = Formula & {
    A: Formula,
    B: Formula
}
export type And = Bin & { }
export type Or = Bin & { }

export type VLElem = ASTNode & {
    v: Variable,
    T?: Type
}

export type Quantifier = Formula & {
    vars: Array<VLElem>,
    A: Formula
}
export type UnivQuantifier = Quantifier & { }
export type ExisQuantifier = Quantifier & { }

export type Imp = Formula & {
    A: Formula,
    B: Formula
}
export type Implies = Imp & { }
export type Iff = Imp & { }

export type Comparison = Formula & {
    op: InfixSymbol,
    x: Term,
    y: Term,
}

export type Predicate = Formula & {
    pred: PredicateSymbol,
    terms: Array<Term>
}

export type Term = ASTNode & { }
export type Function = Term & {
    fn: FunctionSymbol,
    terms: Array<Term>
}
export type IntLiteral = Term & {
    x: number
}
export type Infix = Term & {
    x: Term,
    y: Term
}
export type InfixApplication = Infix & {
    fn: InfixSymbol
}
export type InfixFnApplication = Infix & {
    fn: FunctionSymbol
}
export type ArraySlice = Term & { 
    ident: Variable
}
export type ArrayElem = ArraySlice & {
    idx: Term
}
export type ArrayRange = ArraySlice & {
    begin: Term,
    end: Term
}