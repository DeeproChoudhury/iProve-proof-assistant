import { Token } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule } from 'typescript-parsec';
import { alt, apply, kmid, opt, seq, str, tok, kright, kleft, list_sc, lrec_sc, rep_sc, nil } from 'typescript-parsec';
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

const ATOMIC_TERM = rule<TokenKind, AST.PrefixApplication | AST.ParenTerm | AST.ArrayElem | AST.ArraySlice | AST.Variable>();
const PREFIX_APPLY = rule<TokenKind, AST.PrefixApplication>();
const PAREN_TERM = rule<TokenKind, AST.ParenTerm>();
const ARRAY_SLICE = rule<TokenKind, AST.ArraySlice | AST.ArrayElem>();

const TERM = rule<TokenKind, AST.Term>();
interface Quantifier {
    kind: "A" | "E",
    vars: AST.VariableDeclaration[]
}
interface InfixOperator {
    kind: "InfixFunc" | "InfixOp",
    fn: string
}
type TermOperator = Quantifier | InfixOperator | Token<TokenKind.DirEqToken>;
const OPERATOR = rule<TokenKind, TermOperator>();



VARIABLE.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Variable => {
    return { kind: "Variable", ident: s.text }
}));
TYPE.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Type => {
    return { kind: "Type", ident: s.text }
}));
FN_TYPE.setPattern(apply(
    seq(TYPE, kright(str("->"), TYPE)),
    (value: [AST.Type, AST.Type]): AST.FunctionType => {
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
        return { kind: "TypeExt", A: value[0], B: value[1] }
    }
));

ATOMIC_TERM.setPattern(alt(
    VARIABLE,
    PREFIX_APPLY,
    PAREN_TERM,
    ARRAY_SLICE
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
ARRAY_SLICE.setPattern(apply(
    seq(
        alt(PREFIX_APPLY, PAREN_TERM, VARIABLE),
        rep_sc(alt(
            kmid(str("["), seq(apply(nil(), (_) => { return true; }), TERM, nil()), str("]")),
            kmid(str("["), seq(apply(nil(), (_) => { return false; }), opt(TERM), kright(str(".."), opt(TERM))), str(")")),
            ))
    ),
    (value: [AST.Term, [boolean, AST.Term?, AST.Term?][]]): AST.ArrayElem | AST.ArraySlice => {
        let R : AST.ArrayElem | AST.ArraySlice 
            = { kind: "FunctionApplication", appType: "ArraySlice", fn: "???", params: [
                value[0], value[1][0][1], value[1][0][2]
            ] };
        for (let i = 0; i < value[1].length; i++) {
            let prev : AST.Term = (i > 0) ? R : value[0];
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


TERM.setPattern(
    lrec_sc(
        ATOMIC_TERM,
        seq(OPERATOR, ATOMIC_TERM), (x: AST.Term, y: [TermOperator, AST.Term]): AST.Term => {
            // TODO - PRECEDENCE HERE
            return x;
        })
);

OPERATOR.setPattern(alt(
    tok(TokenKind.DirEqToken),
    apply(
        alt(
            tok(TokenKind.InfixSymbol),
            kmid(str("`"), tok(TokenKind.Symbol), str("`"))
        ), (value: Token<TokenKind.InfixSymbol | TokenKind.Symbol>): InfixOperator => {
            return { 
                kind: (value.kind == TokenKind.InfixSymbol) ? "InfixOp" : "InfixFunc",
                fn: value.text }
        }
    ),
    apply(
        seq(
            tok(TokenKind.QntToken),
            kmid(str("("), list_sc(VAR_DEC, str(",")), str(")."))
        ), (value: [Token<TokenKind.QntToken>, AST.VariableDeclaration[]]): Quantifier => {
            return { 
                kind: (value[0].text == "FA") ? "A" : "E",
                vars: value[1] }
        }
    )
));


export function evaluate(line: string): AST.ASTNode {
    return expectSingleResult(expectEOF(PROOF_LINE.parse(lexer.parse(line))));
}

export default evaluate;
