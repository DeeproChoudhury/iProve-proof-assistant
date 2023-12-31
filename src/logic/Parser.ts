import { LITERAL_TYPES } from '@babel/types';
import { Parser, ParserOutput, Token, ParseError, err, opt, rep } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule } from 'typescript-parsec';
import { alt, apply, kmid, opt_sc, seq, str, tok, kright, kleft, list_sc, rep_sc, nil, amb, lrec_sc } from 'typescript-parsec';
import * as AST from "../types/AST"
import { UnifyScope } from '../types/LogicInterface';
import { display, getSelector, mk_var, PrimitiveType } from '../util/trees';
import { unifies } from './unifier';
Error.stackTraceLimit = Infinity;

/**
 * A parser combinator which, given an unsafe (can throw unhandled errors)
 * parser, will handle any error thrown at parse time, and instead 
 * convert this error into a ts-parsec error
 * 
 * @param P - The unsafe parser
 * @returns The safe equivalent of `P`
 * 
 */
function handle<TKind, TResult>(P: Parser<TKind, TResult>): Parser<TKind, TResult> {
    return {
        parse(token: Token<TKind> | undefined): ParserOutput<TKind, TResult> {
            try {
                return P.parse(token)
            } catch (E) {
                console.log((E as Error).message)
                return {
                    successful: false,
                    error: {
                        kind: "Error",
                        pos: token?.pos,
                        message: (E as Error).message
                    }
                }
            }
        }
    }
}

function empty_list_sc<TKind, Elem, Delim>(P: Parser<TKind, Elem>, delim: Parser<TKind, Delim>): Parser<TKind, Elem[]> {
    return if_else(
        kleft(list_sc(P, delim), opt(delim)),
        apply(nil(), () => [])
    )
}

function dangling_list_sc<TKind, Elem, Delim>(P: Parser<TKind, Elem>, delim: Parser<TKind, Delim>): Parser<TKind, Elem[]> {
    return apply(
        seq(kleft(P, delim), rep_sc(kleft(P, delim)), opt(P)),
        ([v1, v2, v3]) => v3 == undefined ? [v1].concat(v2) : [v1].concat(v2).concat([v3])
    )
}

/**
 * A parser combinator which, given a ambiguous parser `P`, will return a
 * deterministic parser which takes the first match of `P`
 * 
 * @param P - The non-deterministic parser
 * @returns The deterministic equivalent of `P`
 * 
 */
function prec<TKind, TResult>(P: Parser<TKind, TResult>): Parser<TKind, TResult> {
    return apply(
        amb(P),
        (x: TResult[]) => x[0]
    )
}

/**
 * A parser combinator which, given two parsers `A` and `B`, returns a parser
 * which runs A and then B **if and only if** A fails, returning the result
 * of A if it succeeded, and B otherwise
 * 
 * @param A - The first parser
 * @param B - The backup parser
 * @returns The parser corresponding to `A else B`
 * 
 */
function if_else<TKind, TResult1, TResult2>(A: Parser<TKind, TResult1>, B: Parser<TKind, TResult2>, isTL: boolean = false)
    : Parser<TKind, TResult1 | TResult2> {
        return {
            parse(token: Token<TKind> | undefined): ParserOutput<TKind, TResult1 | TResult2> {
                let RA = A.parse(token)
                if (RA.successful) return A.parse(token)
                return B.parse(token)
            }
        }
    }

/**
 * A parser combinator which allows debug output to be added to parsers
 * on success
 * 
 * @param P - Parser
 * @param msg - debug message to print alongside parser output
 * @returns Debugging Parser
 * 
 */
function debug<T,S>(P: Parser<T,S>, msg: string): Parser<T,S>
    { return apply(P, (v) => { console.log(msg, v); return v }) }

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
    DataKW,
    CurlyBrace,
    Times,
    Colon,
    Set,
    Predicate,
    Relation,
    Operation,
    Angles
}

const lexer = buildLexer([
    [true, /^(FA|EX)/g, TokenKind.QntToken],
    [true, /^(::=)/g, TokenKind.DirEqToken],
    [true, /^(::)/g, TokenKind.DoubleColon],
    [true, /^(:=)/g, TokenKind.FunDefToken],
    [true, /^(:)/g, TokenKind.Colon],
    [true, /^\|/g, TokenKind.Guard],
    [true, /^(×)/g, TokenKind.Times],
    [true, /^(\.\.)/g, TokenKind.DoubleDot],
    [true, /^(\[\])/g, TokenKind.EmptyArray],
    [true, /^(\]|\[)/g, TokenKind.SquareBrace],
    [true, /^(\}|\{)/g, TokenKind.CurlyBrace],
    [true, /^(\)|\()/g, TokenKind.Paren],
    
    [true, /^(var)/g, TokenKind.VarToken],
    [true, /^(fun)/g, TokenKind.FunToken],
    [true, /^(assume)/g, TokenKind.Assume],
    [true, /^(use)/g, TokenKind.Skolem],
    [true, /^(begin)/g, TokenKind.Begin],
    [true, /^(end)/g, TokenKind.End],
    [true, /^(Set)/g, TokenKind.Set],
    [true, /^(Predicate)/g, TokenKind.Predicate],
    [true, /^(Relation)/g, TokenKind.Predicate],
    [true, /^(Operation)/g, TokenKind.Operation],
    [true, /^(type)/g, TokenKind.TypeKW],
    [true, /^(data)/g, TokenKind.DataKW],
    [true, /^(((\d+)(\.\d+)?)|((\d+)?(\.\d+)))/g, TokenKind.NumberLiteral],

    [true, /^((\+|-|=|>|<|\/|\*|!|&|\||~|\%)+|in)/g, TokenKind.InfixSymbol],
    [true, /^(\w|\d|\_)+/g, TokenKind.Symbol],
    [true, /^\S/g, TokenKind.Misc],
    [false, /^\s+/g, TokenKind.Space]
]);

const VARIABLE = rule<TokenKind, AST.Variable>();
const TYPE = rule<TokenKind, AST.Type>();
const FN_TYPE = rule<TokenKind, AST.FunctionType>();

const PROOF_LINE = rule<TokenKind, AST.Line>();
const FN_DEC = rule<TokenKind, AST.FunctionDeclaration>();
const VAR_DEC = rule<TokenKind, AST.VariableDeclaration>();

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
const TYPED_LITERAL = rule<TokenKind, AST.Variable>();
const UNTYPED_LITERAL = rule<TokenKind, AST.Variable>();

const TERM = rule<TokenKind, AST.Term>();

const ReservedWord = (x: string): boolean => {
   switch(x) {
        case "List": case "Relation": case "Predicate": case "in": case "data":
        case "type": case "Set": case "Operation":
            return true
        default: return x.includes("IProve")
    }
}

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
    has_unary: boolean,
    apply: (x: AST.Term, y: AST.Term | undefined) => AST.Term,
}
type EndOfTerm = {
    kind: "Operator",
    appType: "End",
    left_assoc: false,
    precedence: 0
}
type TermOperator = InfixOperator | UnaryOperator | EndOfTerm;
const OPERATOR = rule<TokenKind, TermOperator>();


VARIABLE.setPattern(handle(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Variable => {
    if (ReservedWord(s.text)) throw new Error(`${s.text} is a reserved word`)
    return { kind: "Variable", ident: s.text }
})));

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
    kmid(str("("), list_sc(TYPE, alt(tok(TokenKind.Times), str(","))), str(")")),
    (value): AST.TupleType =>
        ({ kind: "TupleType", params: value })
));

TYPED_LITERAL.setPattern(apply(
    seq(tok(TokenKind.Symbol), kmid(str("<"), TYPE, str(">"))),
    (v) => ({
        kind: "Variable",
        ident: v[0].text,
        type: (v[0].text == "Nothing") ? {
            kind: "ParamType",
            params: [v[1]],
            ident: "Maybe"
        } : v[1]
    })
))

TYPE.setPattern(alt(
    PRIMITIVE_TYPE,
    PARAM_TYPE,
    LIST_TYPE,
    TUPLE_TYPE
))

UNTYPED_LITERAL.setPattern(
    apply(
        if_else(tok(TokenKind.NumberLiteral), tok(TokenKind.Symbol)),
        (v) => mk_var(v.text)
    )
)


FN_TYPE.setPattern(
    alt(
        handle(apply(
            seq(
                alt(tok(TokenKind.Set), tok(TokenKind.Predicate), tok(TokenKind.Relation), tok(TokenKind.Operation)),
                kmid(str("<"), list_sc(TYPE, str(",")), str(">"))
            ),
            (value: [Token<TokenKind.Set> | Token<TokenKind.Predicate> | Token<TokenKind.Relation> | Token<TokenKind.Operation>, AST.Type[]]): AST.FunctionType => {
                if (value[0].text != "Predicate" && value[1].length > 1)
                    throw new Error(`${value[0].text} can only take one parameter!`)
                return (value[0].text == "Relation")
                ? { 
                    kind: "FunctionType",
                    argTypes: [value[1][0], value[1][0]],
                    retType: PrimitiveType("Bool"),
                    tag: "Relation"
                }
                : (value[0].text == "Operation" 
                    ? { 
                        kind: "FunctionType",
                        argTypes: [value[1][0], value[1][0]],
                        retType: value[1][0],
                        tag: "Operation"
                    }
                    : { 
                        kind: "FunctionType",
                        argTypes: value[1],
                        retType: PrimitiveType("Bool"),
                        tag: (value[0].text == "Set") ? "Set" : "Predicate"
                    })
            }
        )),
        apply(
            seq(
                kmid(opt_sc(str("(")), list_sc(TYPE, str(",")), opt_sc(str(")"))),
                kright(str("->"), TYPE)),
            (value: [AST.Type[], AST.Type]): AST.FunctionType => {
                return { kind: "FunctionType", argTypes: value[0], retType: value[1] }
            }
        )
    ));

FN_DEC.setPattern(handle(apply(
    seq(
        seq(opt_sc(str("partial")), tok(TokenKind.Symbol)),
        kright(str("::"), FN_TYPE)),
    (value: [[Token<TokenKind> | undefined, Token<TokenKind.Symbol>], AST.FunctionType]): AST.FunctionDeclaration => {
        if (ReservedWord(value[0][1].text)) throw new Error(`${value[0][1].text} is a reserved word`)
        return { kind: "FunctionDeclaration", symbol: value[0][1].text, type: value[1], partial: !(!value[0][0]) }
    }
)));
VAR_DEC.setPattern(handle(apply(
    seq(
        seq(alt(str("const"), str("var"), str("pure")), VARIABLE),
        opt_sc(kright(str(":"), TYPE))),
    (value: [[Token<TokenKind>, AST.Variable], AST.Type | undefined]): AST.VariableDeclaration => {
        let pure = value[0][0].text == "pure";
        if (pure && !value[1]) throw new Error("Pure variables must be explicitly typed")
        return { kind: "VariableDeclaration", symbol: value[0][1], type: value[1], vis: (value[0][0].text as "const"|"var"|"pure") }
    }
)));

VAR_BIND.setPattern(alt(
    apply(
        seq(VARIABLE, kright(str(":"), TYPE)),
        (value: [AST.Variable, AST.Type | undefined]): AST.VariableBinding => {
            return { kind: "VariableBinding", symbol: value[0], type: value[1] }
        }
    ),
    apply(
        seq(VARIABLE, seq(alt(str(">="), str("<="), str("<"), str(">")), VARIABLE)),
        (value: [AST.Variable, [Token<TokenKind>, AST.Variable]]): AST.VariableBinding => {
            let i = parseInt(value[1][1].ident);
            let bt_ = value[1][0].text
            let bt: ">=" | "<=" | "<" | ">" = (bt_ == ">=" || bt_ == "<=" || bt_ == "<") ? bt_ : ">"
            return { kind: "VariableBinding", symbol: value[0], type: PrimitiveType("Int"), bound: i, boundType: bt }
        }
    ),
));

PREFIX_APPLY.setPattern(handle(apply(
    seq(
        alt(
            kmid(str("("), tok(TokenKind.InfixSymbol), str(")")),
            tok(TokenKind.Symbol)
        ),
        opt(kmid(str("<"), list_sc(TYPE, str(",")), str(">"))),
        kmid(str("("), empty_list_sc(TERM, str(",")), str(")"))
    ),    
    (value: [Token<TokenKind.InfixSymbol | TokenKind.Symbol>, AST.Type[] | undefined, AST.Term[]]): AST.PrefixApplication => {
        if (ReservedWord(value[0].text)) throw new Error(`${value[0].text} is a reserved word`)
        return { 
            kind: "FunctionApplication",
            fn: value[0].text,
            params: value[2],
            typeParams: value[1],
            appType: (value[0].kind === TokenKind.Symbol) ? "PrefixFunc" : "PrefixOp"
         }
    }
)));

PAREN_TERM.setPattern(apply(
    alt(
        kright(str("["), seq(TERM, str("]"))),
        kright(str("("), seq(TERM, str(")")))
    ),
    (value: [AST.Term, Token<TokenKind>]): AST.ParenTerm => {
        return { kind: "ParenTerm", term: value[0], isSquare: value[1].text == "]" }
    }
));

ATOMIC_TERM.setPattern(apply(
    seq(
        if_else(
            alt(TYPED_LITERAL, PREFIX_APPLY),
            if_else(if_else(ARRAY_LITERAL, UNTYPED_LITERAL), PAREN_TERM)
        ),
        rep_sc(alt(
            kmid(str("["), seq(apply(nil(), (_) => { return true; }), TERM, nil()), str("]")),
            kmid(str("["), seq(apply(nil(), (_) => { return false; }), TERM, kright(str(".."), opt_sc(TERM))), str(")")),
            ))
    ),
    (value: [AtomicTerm, [boolean, AST.Term, AST.Term?][]]): AtomicTerm => {
        let R : AtomicTerm = value[0];
        for (let i = 0; i < value[1].length; i++) {
            let prev : AST.Term = (R) ? R : value[0];
            const arg0 = value[1][i][0];
            const arg1 = value[1][i][1];
            const arg2 = value[1][i][2]; // Have to put this in a variable for narrowing to work
            // hack, find a more elegant way to structure in general
            if (arg0)
                R = { kind: "FunctionApplication", appType: "ArrayElem", fn: "ArraySelect", params: [
                    // HACK - prev is returned in an error state, value should always be defined
                    prev, (value[1][i][1] ?? prev)
                ] };
            else if (arg2)
                R = { kind: "FunctionApplication", appType: "ArraySlice", fn: "ArraySlice", params: [prev, arg1, arg2] };
            else 
                R = { kind: "FunctionApplication", appType: "ArraySlice", fn: "ArraySlice", params: [prev, arg1] };
        }
        return R;
    }
));


ARRAY_LITERAL.setPattern(apply(
    alt(
        seq(nil(), kmid(str("{"), kleft(list_sc(TERM, str(",")), opt(str(","))), str("}"))),
        seq(nil(), kmid(str("["), dangling_list_sc(TERM, str(",")), str("]"))),
        if_else(
           seq( kmid(seq(str("List"), str("<")), TYPE, seq(str(">"), str("("))),
                kleft(empty_list_sc(TERM, str(",")), str(")"))
                ),
            seq(nil(), kmid(
                seq(str("List"), opt(str("<>")), str("(")),
                kleft(list_sc(TERM, str(",")), opt(str(","))),
                str(")")))
        )
    ),
    (v: [AST.Type | undefined, AST.Term[]]): AST.ArrayLiteral => ({ kind: "ArrayLiteral", elems: v[1], type: v[0] })
));

// PRECEDENCE     IS_BINARY     IS_LEFT_ASSOC     HAS_UNARY_BACKUP
const precedence_table: {[name: string]: [number, boolean, boolean, boolean]} = {
    "~": [10, false, false, true],
    "!": [10, false, false, true],

    "*": [8, true, true, false],
    "/": [8, true, true, false],

    "+": [7, true, true, true],
    "-": [7, true, true, true],
    "++": [7, true, true, false],
    ":": [7, true, true, false],

    "=": [6, true, true, false],
    "in": [6, true, true, false],

    "&": [5, true, true, false],
    "||": [5, true, true, false],
    "^": [5, true, true, false],
    

    "->": [4, true, true, false],
    "<->": [4, true, true, false],
}

TERM.setPattern(
    apply(
        seq(
            rep_sc(OPERATOR),
            ATOMIC_TERM,
            rep_sc(
                seq(
                    seq(OPERATOR, rep_sc(OPERATOR)),
                    ATOMIC_TERM,
                )
            )
        ),
        (value: [TermOperator[], AtomicTerm, [[TermOperator, TermOperator[]], AtomicTerm][]]): AST.Term => {
            let head: AST.Term = value[1]
            let queue: (TermOperator | AST.Term)[] = value[0]
            queue = queue.concat([head]).concat(value[2].map(
                ([[op, ops], term]: [[TermOperator, TermOperator[]], AtomicTerm]) => {
                    let R: (AST.Term | TermOperator)[] = [op]
                    return R.concat(ops).concat(term)
                }
            ).flat())
            queue.push({ kind: "Operator", appType: "End", left_assoc: false, precedence: 0 });
            let out_stack: AST.Term[] = [];
            let op_stack: TermOperator[] = [];

            let prev_atom = false;
            let pt: TermOperator | AST.Term | undefined = undefined;
            for (let token of queue) {
                if (token.kind == "Operator" && token.appType == "Binary" && token.has_unary) {
                    if (!pt || pt.kind == "Operator") {
                        let cached_fn = token.apply
                        token = { 
                            kind: "Operator",
                            appType: "Unary",
                            left_assoc: token.left_assoc,
                            precedence: 10,
                            apply: (t: AST.Term): AST.Term => 
                                cached_fn(t, undefined)
                        }
                    }
                }
                pt = token;

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
                                    if (!x) 
                                        throw new Error("Expected 1 argument, got none");
                                    out_stack.push(stack_top.apply(x));
                                    break;
                                } case "Binary": {
                                    let y = out_stack.pop();
                                    let x = out_stack.pop();
                                    if (!y || !x)
                                        throw new Error("Expected 2 arguments, got 1 or none")
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
                        if (prev_atom) {
                            let fname = out_stack.pop()
                            if (!fname || fname.kind != "Variable") 
                                throw new Error("Cannot apply Term to Term")
                        } else {
                            prev_atom = true;
                            out_stack.push(token);
                            break;
                        }
                    }
                }
            }
            if (out_stack.length > 1) 
                throw new Error("Cannot apply Term to Term")
            if (out_stack.length < 1)
                throw new Error("Malformed Term")

            return out_stack[0];
        })
);

OPERATOR.setPattern(alt(
    apply(
        alt(
            tok(TokenKind.Colon),
            tok(TokenKind.InfixSymbol),
            kmid(str("`"), tok(TokenKind.Symbol), str("`"))
        ), (value: Token<TokenKind.Colon | TokenKind.InfixSymbol | TokenKind.Symbol>): UnaryOperator | InfixOperator => {
            return ((!precedence_table[value.text]) || precedence_table[value.text][1]) 
            ? { 
                kind: "Operator",
                appType: "Binary",
                precedence: (precedence_table[value.text]) ? precedence_table[value.text][0] : 8,
                left_assoc: (precedence_table[value.text]) ? precedence_table[value.text][2] : true,
                has_unary: (precedence_table[value.text]) ? precedence_table[value.text][3] : false,
                apply: (x: AST.Term, y: AST.Term | undefined): AST.Term => {
                    if (!y) {
                        if (!precedence_table[value.text][3])
                            throw new Error("Expected 2 arguments, got 1")
                            return {
                                kind: "FunctionApplication",
                                appType: "UnaryOp",
                                fn: value.text,
                                params: [x]
                            };
                    }
                    return {
                        kind: "FunctionApplication",
                        appType: (value.kind === TokenKind.InfixSymbol || value.kind === TokenKind.Colon) ? "InfixOp" : "InfixFunc",
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
            //console.log(value)
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
                    if (t.kind == "ParenTerm"
                        && !t.isSquare)
                        throw new Error("Quantifiers must be followed by square braces");
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

SKOLEM.setPattern(handle(apply(
    kright(str("use"), TERM),
    (value: AST.Term): AST.Skolemize => {
        if (value.kind != "QuantifierApplication" || value.quantifier != "E")
            throw new Error("`use` must be followed by an existential quantifier")
        return { kind: "Skolemize", arg: value }
    }
)))

BEGIN_SCOPE.setPattern(apply(
    str("begin"),
    (_): AST.BeginScope => ({ kind: "BeginScope" })
))

END_SCOPE.setPattern(apply(
    str("end"),
    (_): AST.EndScope => ({ kind: "EndScope" })
))

const PATTERN = rule<TokenKind, AST.Pattern>();
const CONS_PARAM = rule<TokenKind, AST.ConsParam>();
CONS_PARAM.setPattern(apply(
    seq(
        PATTERN,
        kright(tok(TokenKind.Colon), PATTERN)
    ),
    (value): AST.ConsParam => 
        ({ kind: "ConsParam", A: value[0], B: value[1] })
));
const CONSTRUCTED_TYPE = rule<TokenKind, AST.ConstructedType>();
// below
const TUPLE_PATTERN = rule<TokenKind, AST.TuplePattern>();
// below
const EMPTY_LIST = rule<TokenKind, AST.EmptyList>();
EMPTY_LIST.setPattern(apply(
    alt(seq(str("{"), str("}")), str("[]")),
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
GUARD_TERM.setPattern(if_else(
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
    (value: [AST.Variable, AST.Type[]]): AST.TypeConstructor =>
        { return { kind: "TypeConstructor", ident: value[0].ident, params: value[1],
            selectors: [] }}
))

const TYPE_DEF = rule<TokenKind, AST.TypeDef>();
TYPE_DEF.setPattern(apply(
    seq(
        kmid(tok(TokenKind.DataKW), 
        seq(VARIABLE, rep_sc(VARIABLE)), str("=")),
        list_sc(TYPE_CONSTRUCTOR, str("|"))
    ),
    (value): AST.TypeDef => {
        return { kind: "TypeDef", ident: value[0][0].ident, params: value[0][1].map(x => x.ident),
            cases: value[1].map((C) => { C.selectors = C.params.map((_, j) => getSelector(j, C.ident)); return C}) }
    }
))

const TYPE_DEC = rule<TokenKind, AST.SortDeclaration>();
TYPE_DEC.setPattern(apply(
    seq(kright(tok(TokenKind.TypeKW), VARIABLE), opt(tok(TokenKind.NumberLiteral))),
    (value): AST.SortDeclaration => {
        return { kind: "SortDeclaration", symbol: value[0], arity: parseInt(value[1]?.text ?? "0") }
    }
))


const LANG = rule<TokenKind, AST.Line>();
LANG.setPattern(alt(
    FN_DEC,
    VAR_DEC,
    TYPE_DEC,
    TYPE_DEF
))

CORE.setPattern(alt(
    FN_DEF,
    TERM
));


PROOF_LINE.setPattern(handle(alt(
    CORE,
    LANG,
    TACTIC
)));


/**
 * The main entry point for the FOL parser. Given a string, returns either
 * the AST which results from parsing it as a line in the iProve language
 * syntax, or a ParseError.
 * 
 * @param line - The iProve language line to parse
 * @returns An iProve AST or ParseError
 * 
 */
export function evaluate(line: string): AST.ASTNode | ParseError {
    let A = expectEOF(PROOF_LINE.parse(lexer.parse(line)));
    if (!A.successful) return A.error;
    return expectSingleResult(A);
}

export default evaluate;
