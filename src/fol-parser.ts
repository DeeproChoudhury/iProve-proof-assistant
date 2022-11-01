import { Token } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule } from 'typescript-parsec';
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
    DirEqToken
}

const lexer = buildLexer([
    [true, /^(FA|EX)/g, TokenKind.QntToken],
    [true, /^(\:\:\=)/g, TokenKind.DirEqToken],
    [true, /^(\.\.)/g, TokenKind.DoubleDot],
    [true, /^(\:\:)/g, TokenKind.DoubleColon],
    [true, /^(var)/g, TokenKind.VarToken],
    [true, /^\d+/g, TokenKind.NumberLiteral],
    [true, /^\w+/g, TokenKind.Symbol],
    [true, /^((\-\>)|(\<\-\>))/g, TokenKind.ImpOperator],
    [true, /^(\+|\-|\=|\>|\<|\/|\.|\*|\!|\&|\||\~)+/g, TokenKind.InfixSymbol],
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

type AtomicTerm = AST.PrefixApplication | AST.ParenTerm | AST.ArrayElem | AST.ArraySlice | AST.Variable
const ATOMIC_TERM = rule<TokenKind, AtomicTerm>();
const PREFIX_APPLY = rule<TokenKind, AST.PrefixApplication>();
const PAREN_TERM = rule<TokenKind, AST.ParenTerm>();

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
TYPE.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Type => {
    return { kind: "Type", ident: s.text }
}));
FN_TYPE.setPattern(apply(
    seq(
        kmid(opt(str("(")), list_sc(TYPE, str(",")), opt(str(")"))),
        kright(str("->"), TYPE)),
    (value: [AST.Type[], AST.Type]): AST.FunctionType => {
        return { kind: "FunctionType", A: value[0], B: value[1] }
    }
));


PROOF_LINE.setPattern(alt(
    FN_DEC,
    VAR_DEC,
    TYPE_EXT,
    TERM
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
        kright(opt(str("var")), VARIABLE),
        kright(str(":"), TYPE)),
    (value: [AST.Variable, AST.Type | undefined]): AST.VariableDeclaration => {
        return { kind: "VariableDeclaration", symbol: value[0], type: value[1] }
    }
));
TYPE_EXT.setPattern(apply(
    seq(
        kleft(TYPE, str("⊆")), 
        TYPE),
    (value: [AST.Type, AST.Type]): AST.TypeExt => {
        return { kind: "TypeExt", A: value[0], B: value[1] }
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
            appType: (value[0].kind == TokenKind.Symbol) ? "PrefixFunc" : "PrefixOp"
         }
    }
));
PAREN_TERM.setPattern(apply(
    kmid(str("["), TERM, str("]")),
    (value: AST.Term): AST.ParenTerm => {
        return { kind: "ParenTerm", x: value }
    }
));
ATOMIC_TERM.setPattern(apply(
    seq(
        alt(PREFIX_APPLY, PAREN_TERM, VARIABLE),
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
            if (value[1][i][1])
                R = { kind: "FunctionApplication", appType: "ArraySlice", fn: "???", params: [
                    prev, value[1][i][1], value[1][i][2]
                ] };
            else
                R = { kind: "FunctionApplication", appType: "ArrayElem", fn: "select", params: [
                    // HACK - prev is returned in an error state, value should always be defined
                    prev, (value[1][i][1] ?? prev)
                ] };
                
        }
        return R;
    }
));

// PRECEDENCE     IS_BINARY     IS_LEFT_ASSOC 
const precedence_table: {[name: string]: [number, boolean, boolean]} = {
    "~": [10, false, true],
    "!": [10, false, true],

    "+": [8, true, true],
    "-": [8, true, true],
    "++": [8, true, true],
    "=": [8, true, true],

    "&": [6, true, true],
    "|": [6, true, true],
    "^": [6, true, true],

    "->": [4, true, true],
    "<->": [4, true, true],

    "::=": [3, true, true],
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
                                || (stack_top.precedence == token.precedence && token.left_assoc)
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
                                } case "End": { }
                            }
                            stack_top = op_stack.pop();
                        }
                        op_stack.push(token);
                        break;
                    }
                    case "FunctionApplication":
                    case "ParenTerm":
                    case "EquationTerm":
                    case "Variable":
                    case "QuantifierApplication": {
                        if (prev_atom) throw new Error("Syntax Error: Cannot apply Term to Term");
                        prev_atom = true;
                        out_stack.push(token);
                        break;
                    }
                }
            }
            if (out_stack.length != 1) throw new Error("Syntax Error: Cannot apply Term to Term");
            return out_stack[0];
        })
);

OPERATOR.setPattern(alt(
    apply(
        alt(
            tok(TokenKind.DirEqToken),
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
                        appType: (value.kind == TokenKind.InfixSymbol) ? "InfixOp" : "InfixFunc",
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
                        appType: (value.kind == TokenKind.InfixSymbol) ? "UnaryOp" : "UnaryFunc",
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
            kmid(str("("), list_sc(VAR_DEC, str(",")), str(")."))
        ), (value: [Token<TokenKind.QntToken>, AST.VariableDeclaration[]]): UnaryOperator => {
            return { 
                kind: "Operator",
                appType: "Unary",
                left_assoc: false,
                precedence: 5,
                apply: (t: AST.Term): AST.Term => {
                    return {
                        kind: "QuantifierApplication",
                        term: t,
                        vars: value[1],
                        quantifier: (value[0].text == "FA") ? "A" : "E"
                    };
                } }
        }
    )
));


export function evaluate(line: string): AST.ASTNode | undefined {
    let A = expectEOF(PROOF_LINE.parse(lexer.parse(line)));
    if (!A.successful) return undefined;
    //console.log(A.candidates);
    return expectSingleResult(expectEOF(PROOF_LINE.parse(lexer.parse(line))));
}

export default evaluate;

//const util = require("util");
//console.log(util.inspect(evaluate("f(x, ~b + a) + y"), false, null, true));
