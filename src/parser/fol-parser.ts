import { opt_sc, Token } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule, ParseError } from 'typescript-parsec';
import { alt, apply, kmid, opt, seq, str, tok, kright, kleft, list_sc, rep_sc, nil } from 'typescript-parsec';
import * as AST from './AST'
Error.stackTraceLimit = Infinity;


enum TokenKind {
    NumberLiteral,
    Symbol,
    InfixSymbol,
    NegToken,
    PropOperator,
    ImpOperator,
    QntToken,
    DoubleDot,
    DoubleColon,
    VarToken,
    Misc,
    Space,
    DirEqToken,
    SquareBrace,
    FunToken,
    Assume,
    End,
    Begin,
    Skolem,
    FunDefToken,
    EmptyArray,
    Paren,
    Guard,
    TypeKW,
    CurlyBrace
}

const lexer = buildLexer([
    [true, /^(FA|EX)/g, TokenKind.QntToken],
    [true, /^(::=)/g, TokenKind.DirEqToken],
    [true, /^(:=)/g, TokenKind.FunDefToken],
    [true, /^(\.\.)/g, TokenKind.DoubleDot],
    [true, /^(::)/g, TokenKind.DoubleColon],
    [true, /^(\[\])/g, TokenKind.EmptyArray],
    [true, /^(\]|\[)/g, TokenKind.SquareBrace],
    [true, /^(\}|\{)/g, TokenKind.CurlyBrace],
    [true, /^(\)|\()/g, TokenKind.Paren],
    [true, /^(var)/g, TokenKind.VarToken],
    [true, /^(fun)/g, TokenKind.FunToken],
    [true, /^(assume)/g, TokenKind.Assume],
    [true, /^(skolem)/g, TokenKind.Skolem],
    [true, /^(begin)/g, TokenKind.Begin],
    [true, /^(end)/g, TokenKind.End],
    [true, /^(type)/g, TokenKind.TypeKW],
    [true, /^(\|)/g, TokenKind.Guard],

    [true, /^(\w|\d|\_)+/g, TokenKind.Symbol],
    [true, /^(\+|-|=|>|<|\/|\.|\*|!|&|\||~)+/g, TokenKind.InfixSymbol],
    [true, /^\S/g, TokenKind.Misc],
    [false, /^\s+/g, TokenKind.Space]
]);

const VARIABLE = rule<TokenKind, AST.Variable>();
const TYPE = rule<TokenKind, AST.Type>();
const FN_TYPE = rule<TokenKind, AST.FunctionType>();

const PROOF_LINE = rule<TokenKind, AST.Line>();
const FN_DEC = rule<TokenKind, AST.FunctionDeclaration>();
const VAR_DEC = rule<TokenKind, AST.VariableDeclaration>();
const TYPE_EXT = rule<TokenKind, AST.TypeExt>();

const VAR_BIND = rule<TokenKind, AST.VariableBinding>();

type AtomicTerm = AST.PrefixApplication | AST.ParenTerm | AST.ArrayElem | AST.ArraySlice | AST.Variable | AST.ArrayLiteral
const ATOMIC_TERM = rule<TokenKind, AtomicTerm>();
const ARRAY_LITERAL = rule<TokenKind, AST.ArrayLiteral>();
const PREFIX_APPLY = rule<TokenKind, AST.PrefixApplication>();
const PAREN_TERM = rule<TokenKind, AST.ParenTerm>();

const ASSUMPTION = rule<TokenKind, AST.Assumption>();
const SKOLEM = rule<TokenKind, AST.Skolemize>();
const BEGIN_SCOPE = rule<TokenKind, AST.BeginScope>();
const END_SCOPE = rule<TokenKind, AST.EndScope>();
const TACTIC = rule<TokenKind, AST.Tactic>();
const CORE = rule<TokenKind, AST.Line>();

const TERM = rule<TokenKind, AST.Term>();
interface UnaryOperator {
    kind: "Operator",
    appType: "Unary",
    precedence: number,
    left_assoc: boolean,
    apply: (t: AST.Term) => AST.Term,
}
interface InfixOperator {
    kind: "Operator",
    appType: "Binary",
    precedence: number,
    left_assoc: boolean,
    apply: (x: AST.Term, y: AST.Term) => AST.Term,
}
type EndOfTerm = {
    kind: "Operator",
    appType: "End",
    left_assoc: false,
    precedence: 0
}
type TermOperator = InfixOperator | UnaryOperator | EndOfTerm;
const OPERATOR = rule<TokenKind, TermOperator>();


VARIABLE.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Variable => {
    return { kind: "Variable", ident: s.text }
}));

const PRIMITIVE_TYPE = rule<TokenKind, AST.PrimitiveType>();
const PARAM_TYPE = rule<TokenKind, AST.ParamType>();
const LIST_TYPE = rule<TokenKind, AST.ListType>();
const TUPLE_TYPE = rule<TokenKind, AST.TupleType>();


PRIMITIVE_TYPE.setPattern(apply(
    tok(TokenKind.Symbol),
    (s: Token<TokenKind.Symbol>): AST.PrimitiveType =>
        ({ kind: "PrimitiveType", ident: s.text })
));

PARAM_TYPE.setPattern(apply(
    seq(
        tok(TokenKind.Symbol),
        kmid(str("<"), list_sc(TYPE, str(",")), str(">")),
    ),
    (value): AST.ParamType =>
        ({ kind: "ParamType", ident: value[0].text, params: value[1] })
));

LIST_TYPE.setPattern(apply(
    kmid(str("["), TYPE, str("]")),
    (t): AST.ListType =>
        ({ kind: "ListType", param: t })
));

TUPLE_TYPE.setPattern(apply(
    kmid(str("("), list_sc(TYPE, str(",")), str(")")),
    (value): AST.TupleType =>
        ({ kind: "TupleType", params: value })
));

TYPE.setPattern(alt(
    PRIMITIVE_TYPE,
    PARAM_TYPE,
    LIST_TYPE,
    TUPLE_TYPE
))




FN_TYPE.setPattern(apply(
    seq(
        kmid(opt(str("(")), list_sc(TYPE, str(",")), opt(str(")"))),
        kright(str("->"), TYPE)),
    (value: [AST.Type[], AST.Type]): AST.FunctionType => {
        return { kind: "FunctionType", argTypes: value[0], retType: value[1] }
    }
));

FN_DEC.setPattern(apply(
    seq(
        kright(opt(str("fun")), tok(TokenKind.Symbol)),
        kright(str("::"), FN_TYPE)),
    (value: [Token<TokenKind.Symbol>, AST.FunctionType]): AST.FunctionDeclaration => {
        return { kind: "FunctionDeclaration", symbol: value[0].text, type: value[1] }
    }
));
VAR_DEC.setPattern(apply(
    seq(
        kright(str("var"), VARIABLE),
        opt(kright(str(":"), TYPE))),
    (value: [AST.Variable, AST.Type | undefined]): AST.VariableDeclaration => {
        return { kind: "VariableDeclaration", symbol: value[0], type: value[1] }
    }
));
TYPE_EXT.setPattern(apply(
    seq(
        kleft(TYPE, str("⊆")), 
        TYPE),
    (value: [AST.Type, AST.Type]): AST.TypeExt => {
        return { kind: "TypeExt", subType: value[0], superType: value[1] }
    }
));

VAR_BIND.setPattern(apply(
    seq(VARIABLE, opt(kright(str(":"), TYPE))),
    (value: [AST.Variable, AST.Type | undefined]): AST.VariableBinding => {
        return { kind: "VariableBinding", symbol: value[0], type: value[1] }
    }
));

PREFIX_APPLY.setPattern(apply(
    seq(
        alt(
            kmid(str("("), tok(TokenKind.InfixSymbol), str(")")),
            tok(TokenKind.Symbol)
        ),
        kmid(str("("), list_sc(TERM, str(",")), str(")"))
    ),    
    (value: [Token<TokenKind.InfixSymbol | TokenKind.Symbol>, AST.Term[]]): AST.PrefixApplication => {
        return { 
            kind: "FunctionApplication",
            fn: value[0].text,
            params: value[1],
            appType: (value[0].kind === TokenKind.Symbol) ? "PrefixFunc" : "PrefixOp"
         }
    }
));
PAREN_TERM.setPattern(apply(
    kmid(str("["), TERM, str("]")),
    (value: AST.Term): AST.ParenTerm => {
        return { kind: "ParenTerm", term: value }
    }
));
ATOMIC_TERM.setPattern(apply(
    seq(
        alt(PREFIX_APPLY, PAREN_TERM, VARIABLE, ARRAY_LITERAL),
        rep_sc(alt(
            kmid(str("["), seq(apply(nil(), (_) => { return true; }), TERM, nil()), str("]")),
            kmid(str("["), seq(apply(nil(), (_) => { return false; }), opt(TERM), kright(str(".."), opt(TERM))), str(")")),
            ))
    ),
    (value: [AtomicTerm, [boolean, AST.Term?, AST.Term?][]]): AtomicTerm => {
        let R : AtomicTerm = value[0];
        for (let i = 0; i < value[1].length; i++) {
            let prev : AST.Term = (R) ? R : value[0];
            // hack, find a more elegant way to structure in general
            if (value[1][i][0])
                R = { kind: "FunctionApplication", appType: "ArrayElem", fn: "select", params: [
                    // HACK - prev is returned in an error state, value should always be defined
                    prev, (value[1][i][1] ?? prev)
                ] };
            else
                R = { kind: "FunctionApplication", appType: "ArraySlice", fn: "???", params: [
                    prev, value[1][i][1], value[1][i][2]
                ] };   
        }
        return R;
    }
));
ARRAY_LITERAL.setPattern(apply(
    kmid(str("{"), list_sc(TERM, str(",")), str("}")),
    (v): AST.ArrayLiteral => ({ kind: "ArrayLiteral", elems: v })
));

// PRECEDENCE     IS_BINARY     IS_LEFT_ASSOC 
const precedence_table: {[name: string]: [number, boolean, boolean]} = {
    "~": [10, false, false],
    "!": [10, false, false],

    "*": [8, true, true],
    "/": [8, true, true],

    "+": [7, true, true],
    "-": [7, true, true],
    "++": [7, true, true],
    "=": [7, true, true],

    "&": [6, true, true],
    "|": [6, true, true],
    "^": [6, true, true],

    "->": [4, true, true],
    "<->": [4, true, true],
}

TERM.setPattern(
    apply(
        seq(alt(OPERATOR, ATOMIC_TERM), rep_sc(alt(OPERATOR, ATOMIC_TERM))),
        (value: [TermOperator | AST.Term,  (TermOperator | AST.Term)[]]): AST.Term => {
            let queue: (TermOperator | AST.Term)[] = [value[0]].concat(value[1]);
            queue.push({ kind: "Operator", appType: "End", left_assoc: false, precedence: 0 });
            let out_stack: AST.Term[] = [];
            let op_stack: TermOperator[] = [];

            let prev_atom = false;
            for (let token of queue) {
                //console.log(token, out_stack, op_stack);
                switch (token.kind) {
                    case "Operator": {
                        prev_atom = false;
                        let stack_top = op_stack.pop();
                        while (stack_top) {
                            //console.log("HERE 2", stack_top);
                            let overrule = stack_top.precedence > token.precedence
                                || (stack_top.precedence === token.precedence && token.left_assoc)
                            if (!overrule) { op_stack.push(stack_top); break;}
                            //console.log("HERE", stack_top);

                            switch (stack_top.appType) {
                                case "Unary": {
                                    let x = out_stack.pop();
                                    if (!x) throw new Error("Syntax Error: Expected 1 argument, got none");
                                    out_stack.push(stack_top.apply(x));
                                    break;
                                } case "Binary": {
                                    let y = out_stack.pop();
                                    let x = out_stack.pop();
                                    if (!x || !y) throw new Error("Syntax Error: Expected 2 arguments, got 1 or none");
                                    out_stack.push(stack_top.apply(x, y));
                                    break;
                                } case "End": { }
                            }
                            stack_top = op_stack.pop();
                        }
                        op_stack.push(token);
                        break;
                    }
                    default: {
                        if (prev_atom) throw new Error("Syntax Error: Cannot apply Term to Term");
                        prev_atom = true;
                        out_stack.push(token);
                        break;
                    }
                }
            }
            if (out_stack.length > 1) throw new Error("Syntax Error: Cannot apply Term to Term");
            if (out_stack.length < 1) throw new Error("Syntax Error: Malformed Term");
            return out_stack[0];
        })
);

OPERATOR.setPattern(alt(
    apply(
        alt(
            tok(TokenKind.InfixSymbol),
            kmid(str("`"), tok(TokenKind.Symbol), str("`"))
        ), (value: Token<TokenKind.DirEqToken | TokenKind.InfixSymbol | TokenKind.Symbol>): UnaryOperator | InfixOperator => {
            return ((!precedence_table[value.text]) || precedence_table[value.text][1]) 
            ? { 
                kind: "Operator",
                appType: "Binary",
                left_assoc: (precedence_table[value.text]) ? precedence_table[value.text][2] : true,
                precedence: (precedence_table[value.text]) ? precedence_table[value.text][0] : 8,
                apply: (x: AST.Term, y: AST.Term): AST.Term => {
                    return {
                        kind: "FunctionApplication",
                        appType: (value.kind === TokenKind.InfixSymbol) ? "InfixOp" : "InfixFunc",
                        fn: value.text,
                        params: [x, y]
                    };
                } 
            }
            : { 
                kind: "Operator",
                appType: "Unary",
                left_assoc: precedence_table[value.text][2],
                precedence: precedence_table[value.text][0],
                apply: (t: AST.Term): AST.Term => {
                    return {
                        kind: "FunctionApplication",
                        appType: (value.kind === TokenKind.InfixSymbol) ? "UnaryOp" : "UnaryFunc",
                        fn: value.text,
                        params: [t]
                    };
                } 
            }
        }
    ),
    apply(
        seq(
            tok(TokenKind.QntToken),
            alt(
                kleft(list_sc(VARIABLE, str(",")), str(".")),
                kmid(str("("), list_sc(VAR_BIND, str(",")), kleft(str(")"),str(".")))
                )
        ), (value: [Token<TokenKind.QntToken>, AST.Variable[] | AST.VariableBinding[]]): UnaryOperator => {
            let decs : AST.VariableBinding[] = [];
            for (let v of value[1]) {
                switch (v.kind) {
                    case "Variable": decs.push({kind: "VariableBinding", symbol: v }); break;
                    case "VariableBinding": decs.push(v);
                }
            }
            return { 
                kind: "Operator",
                appType: "Unary",
                left_assoc: false,
                precedence: 9,
                apply: (t: AST.Term): AST.Term => {
                    return {
                        kind: "QuantifierApplication",
                        term: t,
                        vars: decs,
                        quantifier: (value[0].text === "FA") ? "A" : "E"
                    };
                } }
        }
    )
));


ASSUMPTION.setPattern(apply(
    kright(str("assume"), TERM),
    (value: AST.Term): AST.Assumption => ({ kind: "Assumption", arg: value })
))

SKOLEM.setPattern(apply(
    kright(str("skolem"), VARIABLE),
    (value: AST.Variable): AST.Skolemize => ({ kind: "Skolemize", arg: value.ident })
))

BEGIN_SCOPE.setPattern(apply(
    str("begin"),
    (_): AST.BeginScope => ({ kind: "BeginScope" })
))

END_SCOPE.setPattern(apply(
    str("end"),
    (_): AST.EndScope => ({ kind: "EndScope" })
))

const CONS_PARAM = rule<TokenKind, AST.ConsParam>();
CONS_PARAM.setPattern(apply(
    seq(
        VARIABLE,
        kright(tok(TokenKind.DoubleColon), VARIABLE)
    ),
    (value): AST.ConsParam => 
        ({ kind: "ConsParam", A: value[0].ident, B: value[1].ident })
));
const CONSTRUCTED_TYPE = rule<TokenKind, AST.ConstructedType>();
// below
const TUPLE_PATTERN = rule<TokenKind, AST.TuplePattern>();
// below
const EMPTY_LIST = rule<TokenKind, AST.EmptyList>();
EMPTY_LIST.setPattern(apply(
    str("[]"),
    (_): AST.EmptyList => 
        ({ kind: "EmptyList" })
));
const SIMPLE_PARAM = rule<TokenKind, AST.SimpleParam>();
SIMPLE_PARAM.setPattern(apply(
    VARIABLE,
    (value): AST.SimpleParam => 
        ({ kind: "SimpleParam", ident: value.ident })
));

const GUARD = rule<TokenKind, AST.Guard>();

const PATTERN = rule<TokenKind, AST.Pattern>();
PATTERN.setPattern(alt(
    kmid(str("("), CONS_PARAM, str(")")),
    kmid(str("("), CONSTRUCTED_TYPE, str(")")),
    kmid(str("("), TUPLE_PATTERN, str(")")),
    EMPTY_LIST,
    SIMPLE_PARAM
))

CONSTRUCTED_TYPE.setPattern(apply(
    seq(
        VARIABLE,
        rep_sc(PATTERN)
    ),
    (value): AST.ConstructedType => 
        ({ kind: "ConstructedType", c: value[0].ident, params: value[1] })
));

TUPLE_PATTERN.setPattern(apply(
    list_sc(PATTERN, str(",")),
    (value): AST.TuplePattern => 
        ({ kind: "TuplePattern", params: value })
));

const GUARD_TERM = rule<TokenKind, AST.Guard | AST.Term>();
GUARD_TERM.setPattern(alt(
    GUARD,
    TERM
))

GUARD.setPattern(apply(
    seq(
        kright(str("|"), TERM),
        kright(str(":="), TERM),
        opt_sc(GUARD)
    ),
    (value): AST.Guard => 
        ({ kind: "Guard", cond: value[0], res: value[1], next: value[2] })
));


const FN_DEF = rule<TokenKind, AST.FunctionDefinition>();
FN_DEF.setPattern(apply(
    seq(
        VARIABLE,
        rep_sc(PATTERN),
        kright(tok(TokenKind.DirEqToken), GUARD_TERM)
    ),
    (value): AST.FunctionDefinition => 
        ({ kind: "FunctionDefinition", ident: value[0].ident, params: value[1], def: value[2] })
));

TACTIC.setPattern(alt(
    ASSUMPTION,
    SKOLEM,
    BEGIN_SCOPE,
    END_SCOPE
));

const TYPE_CONSTRUCTOR = rule<TokenKind, AST.TypeConstructor>();
TYPE_CONSTRUCTOR.setPattern(apply(
    seq(
        VARIABLE,
        rep_sc(TYPE)
    ),
    (value): AST.TypeConstructor =>
        // TODO: SELECTORS
        ({ kind: "TypeConstructor", ident: value[0].ident, params: value[1], selectors: ["bruh"] })
))

const TYPE_DEF = rule<TokenKind, AST.TypeDef>();
TYPE_DEF.setPattern(apply(
    seq(
        kmid(tok(TokenKind.TypeKW), 
        seq(VARIABLE, rep_sc(VARIABLE)), tok(TokenKind.DirEqToken)),
        list_sc(TYPE_CONSTRUCTOR, str("|"))
    ),
    (value): AST.TypeDef =>
        ({ kind: "TypeDef", ident: value[0][0].ident, params: value[0][1].map(x => x.ident), cases: value[1] })
))

const LANG = rule<TokenKind, AST.Line>();
LANG.setPattern(alt(
    FN_DEC,
    VAR_DEC,
    TYPE_DEF
))

CORE.setPattern(alt(
    FN_DEF,
    TERM
));


PROOF_LINE.setPattern(alt(
    CORE,
    LANG,
    TACTIC
));



export function evaluate(line: string): AST.ASTNode | ParseError {
    try {
        let A = expectEOF(PROOF_LINE.parse(lexer.parse(line)));
        if (!A.successful) return A.error;
        return expectSingleResult(A);
    } catch (E) {
        return { kind: "Error", message: (E as Error).message, pos: undefined }
    }
}

export default evaluate;


let TD = (evaluate("type Listyy ::= Emptyyy | Consyy Listyy") as AST.TypeDef)
let motive = (evaluate("FA (y:Listyy).[Q(x) & Q(y)]") as AST.Term)
let motive2 = (evaluate("FA (y:Listyy).[Q(x) & Q(x)]") as AST.Term)
let motive3 = (evaluate("Q(x)") as AST.Term)
let pt: AST.PrimitiveType = {
    kind: "PrimitiveType",
    ident: "Listyy"
}
const util = require("util")

//console.log(util.inspect(
//    AST.rec_on(pt, TD)('x', motive)
//, false, null, true))
//console.log(AST.display(AST.rec_on(pt, TD)('x', motive)))

AST.LI.newProof();
AST.LI.addGlobal(TD);
console.log(`${AST.LI}`);
AST.LI.newProof();
//console.log(AST.Z3Unifies(AST.rec_on(pt, TD)('x', motive), AST.rec_on(pt, TD)('x', motive2)))
const EMPTY_SCOPE: AST.UnifyScope = {
    kind: "UnifyScope",
    sort_ctx_a: new Map,
    sort_ctx_b: new Map,
    assignments: [new Map]
}
//console.log(util.inspect(AST.unify_preprocess((evaluate("x & FA (x:Int).x") as AST.Term)),
//   false, null, true))
/*
console.log(util.inspect(AST.unifies(
        (evaluate("x & FA (x:Int,y:Int).[x & y]") as AST.Term),
        (evaluate("x & FA (z:Int,y:Int).[y & z]") as AST.Term)
    ),
    false, null, true))
*/
let verdict = AST.unifies(
    (evaluate("x & FA (x:Int,y:Int).[x & y & x & y]") as AST.Term),
    (evaluate("x & FA (z:Int,y:Int).[[y & y] & [z & z]]") as AST.Term)
)
if (verdict.kind == "UnifyFail") {
    console.log("ERROR")
} else {
    console.log(AST.display(verdict.term))
}
/*
console.log(util.inspect(AST.gen_unify((evaluate("x & y") as AST.Term), (evaluate("x & y") as AST.Term), {
    kind: "UnifyScope",
    free_variables: new Set,
    assignments: []
}), false, null, true))
*/
/*
const util = require("util")
let ASTN0 = (evaluate("length :: [Int] -> Int") as AST.FunctionDeclaration)
let ASTN1 = (evaluate("length (_::as) ::= 1 + length(as)")  as AST.FunctionDefinition)
let ASTN2 = (evaluate("length [] ::= 0")  as AST.FunctionDefinition)

let ASTN4 = (evaluate("length(x) > 0") as AST.Term)
let ASTN3 = (evaluate("var x : [Int]") as AST.ASTNode)
console.log(util.inspect(ASTN0, false, null, true));
console.log(util.inspect(ASTN1, false, null, true));
console.log(util.inspect(ASTN2, false, null, true));

AST.LI.addFnDecl(ASTN0);
AST.LI.addFnDef(ASTN1);
AST.LI.addFnDef(ASTN2);

AST.LI.addGiven(ASTN3)

AST.LI.setGoal(ASTN4)

console.log(`${AST.LI}`);
*/

/*
(assert (implies
(and (P (as seq.empty (Seq Int)))
(forall ((x (Seq Int))) (forall ((y Int)) (implies (P x) (P (seq.++ x (seq.unit y)))))))
(forall ((x (Seq Int))) (P x))
))

(assert (P (as seq.empty (Seq Int))))
(assert (forall ((x (Seq Int))) (forall ((y Int)) (implies (P x) (P (seq.++ x (seq.unit y)))))))

(assert (not (forall ((x (Seq Int))) (P x))))
*/