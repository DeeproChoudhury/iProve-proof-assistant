export type ASTNode = Symbol | FunctionType | Line | VLElem | Term | Atom | PropAtom | Clause | InfixOperator | PropOperator | ImpOperator | Formula

export type Symbol = Variable | Type | FunctionSymbol | PredicateSymbol | RawSymbol

export type Variable = { 
    kind: "Variable"
    isAtom: true,
    isSymbol: true,
    isVariable: true,
    ident: String
 }
export type Type = { 
    kind: "Type"
    isSymbol: true,
    ident: String
    isType: true
 }
export type FunctionSymbol = { 
    kind: "FunctionSymbol"
    isSymbol: true,
    isInfixOperator: true,
    isFunctionSymbol: true
    ident: String
 }
export type PredicateSymbol = { 
    kind: "PredicateSymbol"
    isSymbol: true,
    ident: String
    isPredicateSymbol: true
 }
export type RawSymbol = Variable & Type & FunctionSymbol & PredicateSymbol & { 
    isSymbol: true,
    ident: String
    isRawSymbol: true
 }

export type InfixSymbol = {
    kind: "InfixSymbol"
    isInfixOperator: true,
    isInfixSymbol: true,
    ident: String
}

export type FunctionType = {
    kind: "FunctionType",
    isFunctionType: true,
    A: Type,
    B: Type
}

export type Line = TypeExt | Declaration

export type TypeExt = {
    kind: "TypeExt",
    isLine: true,
    isTypeExt: true,
    A: Type,
    B: Type
}

export type Declaration = FunctionDeclaration | VariableDeclaration

export type FunctionDeclaration = {
    kind: "FunctionDeclaration",
    isLine: true,
    isDeclaration: true
    isFunctionDeclaration: true,
    symbol: FunctionSymbol,
    type: FunctionType
}

export type VariableDeclaration = {
    kind: "VariableDeclaration",
    isLine: true,
    isDeclaration: true
    isVariableDeclaration: true,
    symbol: Variable,
    type?: Type
}

export type VLElem = {
    kind: "VLElem",
    isVLElem: true,
    v: Variable,
    T?: Type
}

export type Term = {
    kind: "Term",
    isTerm: true,
    atoms: Array<Atom>,
    operators: Array<InfixOperator>
}

export type Atom = Variable | Function | IntLiteral | ArraySlice | ParenTerm

export type Function = {
    kind: "Function"
    isAtom: true,
    isFunction: true,
    fn: FunctionSymbol,
    terms: Array<Term>
}

export type IntLiteral = {
    kind: "IntLiteral",
    isAtom: true,
    isIntLiteral: true,
    n: number
}

export type InfixOperator = FunctionSymbol | InfixSymbol

export type ArraySlice = ArrayElem | ArrayRange

export type ArrayElem = {
    kind: "ArrayElem",
    isAtom: true,
    isArraySlice: true,
    isArrayElem: true,
    ident: Variable
    idx: Term
}

export type ArrayRange = {
    kind: "ArrayRange",
    isAtom: true,
    isArraySlice: true,
    isArrayRange: true,
    ident: Variable
    begin: Term,
    end: Term
}

export type ParenTerm = { 
    kind: "ParenTerm",
    isAtom: true,
    isParenTerm: true,
    x: Term
}

export type PropAtom = Neg | PropLiteral | Comparison | Predicate | QuantifiedFormula | ParenFormula

 export type Neg = {
    kind: "Neg",
    isPropAtom: true
    isNeg: true,
    A: Formula
}

 export type PropLiteral = {
    kind: "PropLiteral",
    isPropAtom: true
    isPropLiteral: true,
    truth: boolean,
 }

 export type Comparison = {
    kind: "Comparison",
    isPropAtom: true
    isComparison: true,
    op: InfixSymbol,
    x: Term,
    y: Term,
}

export type Predicate = {
    kind: "Predicate",
    isPropAtom: true
    isPredicate: true,
    pred: PredicateSymbol,
    terms: Array<Term>
}

export enum Quantifier {
    E,
    A
}

export type PropOperator = {
    kind: "PropOperator"
    isPropOperator: true,
    op: string
}

export type Clause = QFClause

export type QFClause =  {
    kind: "QFClause"
    isClause: true,
    isQFClause: true,
    atoms: Array<PropAtom>
    operators: Array<PropOperator>
}

export type QuantifiedFormula = {
    kind: "QuantifiedFormula",
    isPropAtom: true
    isQuantifiedFormula: true,
    quantifier: Quantifier,
    vars: Array<VLElem>,
    A: Clause
 }

 export type ImpOperator = {
    kind: "ImpOperator",
    isImpOperator: true,
    op: string
}

export type Formula = {
    kind: "Formula",
    isFormula: true,
    clauses: Array<Clause>,
    operators: Array<ImpOperator>
}

export type ParenFormula = {
    kind: "ParenFormula",
    isPropAtom: true
    isParenFormula: true,
    A: Formula
 }

export type FinalNode =
      Variable
    | FunctionSymbol
    | PredicateSymbol
    | Type
    | InfixSymbol
    | PropOperator
    | ImpOperator
    | FunctionType 
    | TypeExt 
    | FunctionDeclaration 
    | VariableDeclaration 
    | VLElem 
    | Term 
    | Function 
    | IntLiteral 
    | ArrayElem
    | ArrayRange 
    | ParenTerm
    | Neg 
    | PropLiteral 
    | Comparison 
    | Predicate 
    | QFClause 
    | QuantifiedFormula 
    | Formula
    | ParenFormula

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
        case "VLElem": return a.T ? `(${display(a.v)} : ${display(a.T)})` : `(${display(a.v)})`;
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
