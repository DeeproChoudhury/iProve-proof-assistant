import { stateless_map_terms } from "../logic/combinator";
import { fnDisplay } from "../logic/util";
import * as AST from "../types/AST"

function d(a: AST.ASTNode): string {
    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(d).join(", ")}) -> ${d(a.retType)}`;
        case "VariableBinding": return d(a.symbol) + (a.type ? `: ${d(a.type)}` : "");
        case "FunctionDeclaration": return `${a.symbol} :: ${d(a.type)}`;
        case "VariableDeclaration": return `var ${d(a.symbol)}` + (a.type ? `: ${d(a.type)}` : "");
        case "Variable": return a.ident;
        case "FunctionApplication": {
            const fn = fnDisplay(a.fn);
            switch (a.appType) {
                case "PrefixFunc": 
                    return `${fn}${(a.typeParams) ? "<" + a.typeParams.map(d).join(",") + ">" : ""}(${a.params.map(d).join(", ")})`;
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
        case "Guard": return `\n  | ${d(a.cond)} := ${d(a.res)}`
        case "SimpleParam": return `${a.ident}`
        case "ConsParam": return `(${d(a.A)}:${d(a.B)})`
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

        case "ArrayLiteral": return `{ ${a.elems.map(d).join(", ")} }`
    }
}
export const display: (line: AST.ASTNode) => string = d

export const isDeclaration = (line: AST.Line): line is AST.Declaration => (
    line.kind === "FunctionDeclaration"
        || line.kind === "SortDeclaration"
        || line.kind === "VariableDeclaration"
)
export const isTerm = (line: AST.Line): line is AST.Term => (
    line.kind === "Variable"
        || line.kind === "FunctionApplication"
        || line.kind === "QuantifierApplication"
        || line.kind === "EquationTerm"
        || line.kind === "ParenTerm"
)

export function construct_type(con: AST.TypeConstructor, params: AST.Variable[]): AST.PrefixApplication {
    return {
        kind: "FunctionApplication",
        appType: "PrefixFunc",
        fn: con.ident,
        params: params
    }
}

export function mk_var(ident: string): AST.Variable {
    return {
        kind: "Variable",
        ident: ident
    }
}

export function range_over(t: AST.Term, vars: [AST.Variable, AST.Type][]): AST.Term {
    return vars.length ?
    {
        kind: "QuantifierApplication",
        term: parenthesize(t),
        vars: vars.map((v: [AST.Variable, AST.Type]) => ({
            kind: "VariableBinding",
            symbol: v[0],
            type: v[1]
        })),
        quantifier: "A"
    }
    : t
}

export function PrimitiveType(s: string): AST.PrimitiveType {
    return { kind: "PrimitiveType", ident: s }
}

export function ParamType(ident: string, params: AST.Type[]): AST.ParamType {
    return { kind: "ParamType", ident: ident, params: params }
}

export function imply(L: AST.Term | undefined, R: AST.Term): AST.Term {
    if (!L) return R;
    return {
        kind: "FunctionApplication",
        appType: "InfixOp",
        fn: "->",
        params: [parenthesize(L), parenthesize(R)]
    }
}

export function parenthesize(t: AST.Term, isSquare: boolean = true): AST.ParenTerm {
    return {
        kind: "ParenTerm",
        term: t,
        isSquare: isSquare
    }
}

// NOTE: For obvious reasons, this will not rewrite in itself. 
export function strict_rw(goal: AST.Term, L: AST.Term, R: AST.Term): AST.Term {
    let f = (x: AST.Term): AST.Term => {
        let term_equal: Boolean = JSON.stringify(L) == JSON.stringify(x);
        return term_equal ? R : x
    }
    return stateless_map_terms(f)(goal);
}

export function seek_parens(A: AST.Term): AST.Term {
    let c_t: AST.Term = A;
    while (c_t.kind == "ParenTerm") c_t = c_t.term
    return c_t
}

// utility rec function which takes in an array of terms and returns their
    // (left-associative) dis(/con)junction. See above comment to motivate existence.
export function combineTerms(ts_: AST.Line[], conjunct: string = "||"): AST.Term | undefined {
    let ts = [...ts_];
    let A = ts.shift();
    if (!A) return undefined;
    let tail = combineTerms(ts, conjunct);
    if (!isTerm(A)) return tail;
    if (!tail) return A;

    return {
        kind: "FunctionApplication",
        appType: "InfixOp",
        fn: conjunct,
        params: [A, tail]
    }
}
export const disjunct = combineTerms
export const conjunct = (ts: AST.Line[]): AST.Term | undefined => combineTerms(ts, "&")

export const isBlockStart = (line: AST.Line): line is AST.BlockStart => {
    return line.kind === "BeginScope" || line.kind === "VariableDeclaration" || line.kind === "Assumption";
 }
 
 export const isBlockEnd = (line: AST.Line): line is AST.EndScope => {
    return line.kind === "EndScope";
 }

 
 export const toWrapperFunc = (w: AST.BlockStart): ((term: AST.Term) => AST.Term) => {
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
       params: [w.arg, term]
     });
   } else if (w.kind === "BeginScope") {
     return term => term
 } throw "unsupported BlockStart"; // why isn't this unreachable
 }
 
 export function getSelector(n: number): string {
    switch (n) {
        case 0: return "fst";
        case 1: return "snd";
        default: return `elem${n}`;
    }
}