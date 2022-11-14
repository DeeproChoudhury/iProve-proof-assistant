export type ASTNode = Type | FunctionType | VariableBinding | Line

export type Type = { 
    kind: "Type",
    ident: string
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

export type BlockStart = VariableDeclaration | Assumption;

export type Line = TypeExt | Declaration | Term | Assumption | BlockEnd

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

export type Assumption = {
    kind: "Assumption",
    term: Term
} 

export type BlockEnd = {
    kind: "BlockEnd"
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
    params: [Term, Term] | [Term, Term, Term]
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
        case "Type": return a.ident;
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
        case "Assumption": return `assume ${d(a.term)}`
        case "BlockEnd": return "end";
    }
}


export const display: (line: Line) => string = d


export function s(a: ASTNode) : string {
    switch (a.kind) {
        case "Type": return a.ident;
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
        case "Assumption": return "";
        case "BlockEnd": return "";
    }
}

export const ASTSMTLIB2: (line: Line) => string = s;

export const isBlockStart = (line: Line): line is BlockStart => {
   return line.kind === "VariableDeclaration" || line.kind === "Assumption";
}

export const isBlockEnd = (line: Line): line is BlockEnd => {
   return line.kind === "BlockEnd";
}

export const toWrapperFunc = (w: BlockStart): ((term: Term) => Term) => {
  if (w.kind === "VariableDeclaration") {
    return term => ({
      kind: "QuantifierApplication",
      quantifier: "A",
      vars: [{
        kind: "VariableBinding",
        symbol: w.symbol,
        type: w.type
      }],
      term
    });
  } else if (w.kind === "Assumption") {
    return term => ({
      kind: "FunctionApplication",
      appType: "InfixOp",
      fn: "=>",
      params: [w.term, term]
    });
  } else throw "unsupported BlockStart"; // why isn't this unreachable
}

export const isTerm = (line: Line): line is Term => {
  return line.kind === "Variable"
    || line.kind === "FunctionApplication"
    || line.kind === "QuantifierApplication"
    || line.kind === "EquationTerm"
    || line.kind === "ParenTerm"
}
