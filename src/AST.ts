export type ASTNode = Type | FunctionType | Line

export type Type = { 
    kind: "Type",
    ident: string
}

export type FunctionType = {
    kind: "FunctionType",
    argTypes: Type[],
    retType: Type
}

export type Line = TypeExt | Declaration | Term

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
        case "Type": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(d).join(", ")}) -> ${d(a.retType)}`;
        case "TypeExt": return `${d(a.subType)} ⊆ ${d(a.superType)}`;
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
    }
}


export const display: (line: Line) => string = d


export function ASTSMTLIB2(a: ASTNode | undefined) : string {
    if(a === undefined) {
        return "NULL";
    }

    switch (a.kind) {
        case "Type": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(ASTSMTLIB2).join(" ")})  ${ASTSMTLIB2(a.retType)}`;
        case "TypeExt": return `${ASTSMTLIB2(a.subType)} ⊆ ${ASTSMTLIB2(a.superType)}`;
        case "FunctionDeclaration": return `(declare-fun ${a.symbol} ${ASTSMTLIB2(a.type)})`;
        case "VariableDeclaration": return `${ASTSMTLIB2(a.symbol)} ${a.type ? `: ${ASTSMTLIB2(a.type)}` : "Int"}`;
        case "Variable": return a.ident;
        case "FunctionApplication": {
            const fn = fnSMT(a.fn);
            switch (a.appType) {
                case "PrefixFunc": return `(${fn} ${a.params.map(ASTSMTLIB2).join(" ")})`;
                case "PrefixOp": return `(${fn} ${a.params.map(ASTSMTLIB2).join(", ")})`;
                case "InfixFunc": return `(${fn} ${ASTSMTLIB2(a.params[0])} \`\` ${ASTSMTLIB2(a.params[1])})`;
                case "InfixOp": return `(${fn} ${ASTSMTLIB2(a.params[0])}  ${ASTSMTLIB2(a.params[1])})`;
                case "UnaryFunc": return `($\`${fn}\` ${ASTSMTLIB2(a.params[0])})`;
                case "UnaryOp": return `(${fn} ${ASTSMTLIB2(a.params[0])})`;
                case "ArrayElem": return `${ASTSMTLIB2(a.params[0])}[${ASTSMTLIB2(a.params[1])}]`;
                case "ArraySlice": {
                    const p1 = (a.params[1]) ? ASTSMTLIB2(a.params[1]) : "";
                    const p2 = (a.params[2]) ? ASTSMTLIB2(a.params[2]) : "";
                    return `${ASTSMTLIB2(a.params[0])}[${p1}..${p2})`;
                }
            }
        }
        case "QuantifierApplication": return `(${a.quantifier === "E" ? "exists" : "forall"} ((${a.vars.map(ASTSMTLIB2).join(") (")})) ${ASTSMTLIB2(a.term)})`;
        case "EquationTerm": return `${ASTSMTLIB2(a.lhs)} ::= ${ASTSMTLIB2(a.rhs)}`;
        case "ParenTerm": return `(${ASTSMTLIB2(a.term)})`;
    }
    return "NULL"; // TODO: implement the rest of the function using the new AST types
    /*
    switch (a.kind) {
        // case "Variable": return ""
        // case "FunctionSymbol":
        // case "PredicateSymbol":
        case "Variable":
        case "FunctionSymbol":
        case "PredicateSymbol":
        case "Type":
        // Cases for Variable, FunctionSymbol, PredicateSymbol, Type and InfixSymbol are all `a.ident` so we let them fall through to 
        //the first non-empty case: InfixSymbol.
        case "InfixSymbol":
            return `${a.ident}`;
        case "FunctionDeclaration": return `${ASTSMTLIB2(a.symbol)} :: ${ASTSMTLIB2(a.type)}`;
        case "Term": return `${interleave(a.atoms.map(ASTSMTLIB2), a.operators.map(ASTSMTLIB2)).join(" ")}`;
        case "ArrayElem": return `${ASTSMTLIB2(a.ident)}[${ASTSMTLIB2(a.idx)}]`;
        case "VLElem": return a.T ? `(${ASTSMTLIB2(a.v)} : ${ASTSMTLIB2(a.T)})` : `(${ASTSMTLIB2(a.v)} Int)`;
        case "Predicate":
            return `(${ASTSMTLIB2(a.pred)} ${a.terms.map(ASTSMTLIB2).join(" ")})`;
        case "QFClause": return `${interleave(a.atoms.map(ASTSMTLIB2), a.operators.map(ASTSMTLIB2)).join(" ")}`;
        case "Formula": return `${interleave(a.clauses.map(ASTSMTLIB2), a.operators.map(ASTSMTLIB2)).join(" ")}`;
        case "QuantifiedFormula": return `(${a.quantifier === Quantifier.E ? "exists " : "forall "} (${a.vars.map(ASTSMTLIB2).join(" Int) (")}) ${ASTSMTLIB2(a.A)})`
        default: return " ... ";
    }
    */
}

export function declareConstantASTSMTLIB2(a: ASTNode | undefined): string {
    if(a === undefined) {
        return "NULL";
    }
    switch (a.kind) {
        case "VariableDeclaration": return `(declare-const ${ASTSMTLIB2(a.symbol)} ${a.type ? `${ASTSMTLIB2(a.type)}` : "Int"})`;
        default: return "NULL";
    }
}
