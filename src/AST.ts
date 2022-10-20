import { As } from "@chakra-ui/react"

export type ASTNode = { }

export type Symbol = ASTNode & {
    isSymbol: true,
    ident: String
}
export type Variable = Symbol & Atom & { 
    isVariable: true,
 }
export type Type = Symbol & { 
    isType: true
 }
export type FunctionSymbol = Symbol & InfixOperator & { 
    isFunctionSymbol: true
 }
export type PredicateSymbol = Symbol & { 
    isPredicateSymbol: true
 }
export type RawSymbol = Variable & Type & FunctionSymbol & PredicateSymbol & { 
    isRawSymbol: true
 }

export type InfixSymbol = ASTNode & InfixOperator & {
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

export type VLElem = ASTNode & {
    isVLElem: true,
    v: Variable,
    T?: Type
}

export type Term = ASTNode & {
    isTerm: true,
    atoms: Array<Atom>,
    operators: Array<InfixOperator>
}

export type Atom = ASTNode & {
    isAtom: true,
}

export type Function = Atom & {
    isFunction: true,
    fn: FunctionSymbol,
    terms: Array<Term>
}
export type IntLiteral = Atom & {
    isIntLiteral: true,
    n: number
}
export type InfixOperator = {
    isInfixOperator: true,
}
export type ArraySlice = Atom & { 
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

export type ParenTerm = Atom & { 
    isParenTerm: true,
    x: Term
}







export type PropAtom = ASTNode & {
    isPropAtom: true
 }

 export type Neg = PropAtom & {
    isNeg: true,
    A: Formula
}

 export type PropLiteral = PropAtom & {
    isPropLiteral: true,
    truth: boolean,
 }

 export type Comparison = PropAtom & {
    isComparison: true,
    op: InfixSymbol,
    x: Term,
    y: Term,
}

export type Predicate = PropAtom & {
    isPredicate: true,
    pred: PredicateSymbol,
    terms: Array<Term>
}

export enum Quantifier {
    E,
    A
}

export type PropOperator = ASTNode & {
    isPropOperator: true,
    op: string
}

export type Clause = ASTNode & {
    isClause: true,
}

export type QFClause = Clause & {
    isQFClause: true,
    atoms: Array<PropAtom>
    operators: Array<PropOperator>
}

export type QuantifiedFormula = Clause & {
    isQuantifiedFormula: true,
    quantifier: Quantifier,
    vars: Array<VLElem>,
    A: Clause
 }

 export type ImpOperator = ASTNode & {
    isImpOperator: true,
    op: string
}

export type Formula = ASTNode & {
    isFormula: true,
    clauses: Array<Clause>,
    operators: Array<ImpOperator>
}

export type ParenFormula = PropAtom & {
    isParenFormula: true,
    A: Formula
 }