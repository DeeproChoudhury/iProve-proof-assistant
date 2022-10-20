import { As } from '@chakra-ui/react';
import * as assert from 'assert';
import { TypePredicateKind } from 'typescript';
import { Token } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule } from 'typescript-parsec';
import { alt, apply, kmid, opt, seq, str, tok, kright, kleft, list } from 'typescript-parsec';
import * as AST from './AST'

enum TokenKind {
    NumberLiteral,
    Symbol,
    InfixSymbol,
    NegToken,
    BinToken,
    ImpToken,
    QntToken,
    Space,
}

const lexer = buildLexer([
    [true, /^\d+/g, TokenKind.NumberLiteral],
    [true, /^\w+/g, TokenKind.Symbol],
    [true, /^(\+|\-|\=|\>|\<|\/|\.|\*|\!)+/g, TokenKind.InfixSymbol],
    [true, /^\~/g, TokenKind.NegToken],
    [true, /^(\&|\|)/g, TokenKind.BinToken],
    [true, /^((\-\>)|(\<\-\>))/g, TokenKind.ImpToken],
    [true, /^(FA|EX)/g, TokenKind.QntToken],
    [false, /^\s/g, TokenKind.Space]
]);

enum SymbolType {
    Function,
    Variable,
    Type,
    Infix,
    Predicate
}

interface Symbol {
    idx: number,
    ident: string,
    type: SymbolType
}

var symbolTable = new Map<string, Symbol>() ;
var currentSymbol = 0;

function registerSymbol(symbol: string, type: SymbolType): boolean {
    let current = symbolTable.get(symbol);
    if (current) {
        if (current.type != type) {
            throw new Error("Invalid type");
        }
        return true;
    } else {
        symbolTable.set(symbol, {idx: currentSymbol, ident: symbol, type: type})
        currentSymbol++;
    }
    return true;
}

function assignInfixSymbol(value: Token<TokenKind.InfixSymbol>): AST.InfixSymbol {
    let id = value.text;
    registerSymbol(id, SymbolType.Infix);
    return { isInfixSymbol: true, ident: id };
}

function assignFn(value: Token<TokenKind.Symbol>): AST.FunctionSymbol {
    let id = value.text;
    registerSymbol(id, SymbolType.Function);
    return { isSymbol: true, isFunctionSymbol: true, ident: id };
}

function assignVar(value: Token<TokenKind.Symbol>): AST.Variable {
    let id = value.text;
    registerSymbol(id, SymbolType.Variable);
    return { isSymbol: true, isTerm: true, isVariable: true, ident: id };
}

function assignPredicate(value: Token<TokenKind.Symbol>): AST.PredicateSymbol {
    let id = value.text;
    registerSymbol(id, SymbolType.Predicate);
    return { isSymbol: true, isPredicateSymbol: true, ident: id };
}

function assignType(value: Token<TokenKind.Symbol>): AST.Type {
    let id = value.text;
    registerSymbol(id, SymbolType.Type);
    return { isSymbol: true, isType: true, ident: id };
}

function applyIntLiteral(value: [Token<TokenKind> | undefined, Token<TokenKind.NumberLiteral>]): AST.IntLiteral {
    return {
        isIntLiteral: true, isTerm: true,
        x: parseInt(value[1].text) * (value[0] ? -1 : 1)
    }
}

function applyFnDeclaration(value: [AST.FunctionSymbol, AST.FunctionType]): AST.FunctionDeclaration {
    return {
        isDeclaration: true, isFunctionDeclaration: true,
        symbol: value[0],
        type: value[1]
    }
}

function applyVarDeclaration(value: [AST.Variable, AST.Type]): AST.VariableDeclaration {
    return {
        isDeclaration: true, isVariableDeclaration: true,
        symbol: value[0],
        type: value[1]
    }
}

function applyTypeExt(value: [AST.Type, AST.Type]): AST.TypeExt {
    return {
        isTypeExt: true,
        A: value[0],
        B: value[1]
    }
}

const PROOF_LINE = rule<TokenKind, AST.ASTNode>();
const TYPE_DEC = rule<TokenKind, AST.Declaration>();
const TYPE_EXT = rule<TokenKind, AST.TypeExt>();
const FN_TYPE = rule<TokenKind, AST.FunctionType>();
const FORMULA = rule<TokenKind, AST.Formula>();
const PROPOSITIONAL_SYMBOL = rule<TokenKind, AST.PropLiteral>();
const NEG_FORMULA = rule<TokenKind, AST.Neg>();
const BINARY_FORMULA = rule<TokenKind, AST.Bin>();
const QUANTIFIED_FORMULA = rule<TokenKind, AST.Quantifier>();
const IMPLICATION = rule<TokenKind, AST.Imp>();
const COMPARISON = rule<TokenKind, AST.Comparison>();
const PREDICATE_FORMULA = rule<TokenKind, AST.Predicate>();
const TERM = rule<TokenKind, AST.Term>();
const TERM_LIST = rule<TokenKind, Array<AST.Term>>();
const V_L_ELEM = rule<TokenKind, AST.VLElem>();
const VAR_LIST = rule<TokenKind, Array<AST.VLElem>>();
const FUNCTION_APPLICATION = rule<TokenKind, AST.Function>();
const INFIX_APPLICATION = rule<TokenKind, AST.InfixApplication>();
const INFIX_FN_APPLICATION = rule<TokenKind, AST.InfixFnApplication>();
const ARRAY_RANGE = rule<TokenKind, AST.ArrayRange>();
const ARRAY_ELEM = rule<TokenKind, AST.ArrayElem>();

const VAR_SYM = rule<TokenKind, AST.Variable>();
const FN_SYM = rule<TokenKind, AST.FunctionSymbol>();
const PREDICATE_SYM = rule<TokenKind, AST.PredicateSymbol>();
const INFIX_SYM = rule<TokenKind, AST.InfixSymbol>();
const VAR_TYPE = rule<TokenKind, AST.Type>();
const INT_LITERAL = rule<TokenKind, AST.IntLiteral>();

VAR_SYM.setPattern(apply(tok(TokenKind.Symbol), assignVar));
FN_SYM.setPattern(apply(tok(TokenKind.Symbol), assignFn));
PREDICATE_SYM.setPattern(apply(tok(TokenKind.Symbol), assignPredicate));
VAR_TYPE.setPattern(apply(tok(TokenKind.Symbol), assignType));

INFIX_SYM.setPattern(apply(tok(TokenKind.InfixSymbol), assignInfixSymbol));

INT_LITERAL.setPattern(
    apply(seq(opt(str('-')), tok(TokenKind.NumberLiteral)), applyIntLiteral)
)

PROOF_LINE.setPattern(
    alt(FORMULA, TYPE_EXT, TYPE_DEC)
)

TYPE_DEC.setPattern(
    alt(
        apply(seq(kleft(FN_SYM, str('::')), FN_TYPE), applyFnDeclaration),
        apply(seq(kleft(VAR_SYM, str(':')), VAR_TYPE), applyVarDeclaration),
    )
)

TYPE_EXT.setPattern(
    apply(seq(VAR_TYPE, kright(str('\subset'), VAR_TYPE)), applyTypeExt)
)

function applyFunctionType(value: [AST.Type, AST.Type]): AST.FunctionType {
    return {
        isFunctionType: true,
        A: value[0],
        B: value[1]
    }
}

FN_TYPE.setPattern(
    apply(seq(VAR_TYPE, kright(alt(str('->'), str('\rightarrow')), VAR_TYPE)),
        applyFunctionType)
)

FORMULA.setPattern(
    alt(
        kmid(str('['), FORMULA, str(']')),
        NEG_FORMULA,
        BINARY_FORMULA,
        QUANTIFIED_FORMULA,
        IMPLICATION,
        COMPARISON,
        PREDICATE_FORMULA,
        PROPOSITIONAL_SYMBOL
    )
)

function applyPropSym(value: Token<TokenKind>): AST.PropLiteral {
    return {
        isFormula: true, isPropLiteral: true,
        truth: value.text == '\top',
    }
}

PROPOSITIONAL_SYMBOL.setPattern(
    apply(alt(str('\top'), str('\bot')), applyPropSym)
)

function applyNegation(value: AST.Formula): AST.Neg {
    return {
        isFormula: true, isNeg: true,
        A: value
    }
}

NEG_FORMULA.setPattern(
    apply(kright(alt(str('\neg'), str('\~')), FORMULA), applyNegation)
)

function applyBinaryFormula(value: [AST.Formula, Token<TokenKind.BinToken>, AST.Formula]): AST.Bin {
    return {
        isBin: true, isFormula: true,
        A: value[0],
        B: value[2],
    }
}

BINARY_FORMULA.setPattern(
    apply(seq(FORMULA, tok(TokenKind.BinToken), FORMULA), applyBinaryFormula)
)

function applyQuantifiedFormula(value: [Token<TokenKind.QntToken>, Array<AST.VLElem>, AST.Formula]): AST.Quantifier {
    return {
        isFormula: true, isQuantifier: true,
        vars: value[1],
        A: value[2],
    }
}

QUANTIFIED_FORMULA.setPattern(
    apply(seq(tok(TokenKind.QntToken), kleft(VAR_LIST, str('.')), FORMULA), applyQuantifiedFormula)
)

function applyImplication(value: [AST.Formula, Token<TokenKind.ImpToken>, AST.Formula]): AST.Imp {
    return {
        isFormula: true, isImp: true,
        A: value[0],
        B: value[2],
    }
}

IMPLICATION.setPattern(
    apply(seq(FORMULA, tok(TokenKind.ImpToken), FORMULA), applyImplication)
)

function applyComparison(value: [AST.Term, AST.InfixSymbol, AST.Term]): AST.Comparison {
    return {
        isComparison: true, isFormula: true,
        x: value[0],
        y: value[2],
        op: value[1]
    }
}

COMPARISON.setPattern(
    apply(seq(TERM, INFIX_SYM, TERM), applyComparison)
)

function applyPredicateFormula(value: [AST.PredicateSymbol, Array<AST.Term>]): AST.Predicate {
    return {
        isFormula: true, isPredicate: true,
        pred: value[0],
        terms: value[1],
    }
}

PREDICATE_FORMULA.setPattern(
    apply(seq(PREDICATE_SYM, kmid(str('('), TERM_LIST, str(')'))), applyPredicateFormula)
)

TERM.setPattern(
    alt(
        kmid(str('('), TERM, str(')')),
        INFIX_APPLICATION,
        FUNCTION_APPLICATION,
        ARRAY_RANGE,
        ARRAY_ELEM,
        VAR_SYM,
        INT_LITERAL
    )
)


TERM_LIST.setPattern(
    list(TERM, str(','))
)

function applyVLElem(value: [AST.Variable, AST.Type] | AST.Variable): AST.VLElem {
    return (Array.isArray(value)) ?
    {
        isVLElem: true,
        v: value[0],
        T: value[1],
    } :
    {
        isVLElem: true,
        v: value
    }
}

V_L_ELEM.setPattern(
    apply(alt(
        VAR_SYM,
        kmid(str('('), seq(VAR_SYM, kright(str(':'), VAR_TYPE)), str(')'))
    ), applyVLElem)
)

VAR_LIST.setPattern(
    list(V_L_ELEM, str(','))
)

function applyFnApplication(value: [AST.FunctionSymbol, Array<AST.Term>]): AST.Function {
    return {
        isFunction: true, isTerm: true,
        fn: value[0],
        terms: value[1]
    }
}

FUNCTION_APPLICATION.setPattern(
    apply(seq(FN_SYM, kmid(str('('), TERM_LIST, str(')'))), applyFnApplication)
)

function applyInfixApplication(value: [AST.Term, AST.InfixSymbol, AST.Term]): AST.InfixApplication {
    return {
        isInfix: true, isInfixApplication: true, isTerm: true,
        x: value[0],
        y: value[2],
        fn: value[1]
    }
}

INFIX_APPLICATION.setPattern(
    apply(seq(TERM, INFIX_SYM, TERM), applyInfixApplication)
)

function applyInfixFnApplication(value: [AST.Term, AST.FunctionSymbol, AST.Term]): AST.InfixFnApplication {
    return {
        isInfix: true, isInfixFnApplication: true, isTerm: true,
        x: value[0],
        y: value[2],
        fn: value[1]
    }
}

INFIX_FN_APPLICATION.setPattern(
    apply(seq(TERM, kmid(str('`'), FN_SYM, str('`')), TERM), applyInfixFnApplication)
)

function applyArrayRange(value: [AST.Variable, [AST.Term, AST.Term]]): AST.ArrayRange {
    return {
        isArrayRange: true, isArraySlice: true, isTerm: true,
        ident: value[0],
        begin: value[1][0],
        end: value[1][1],
        
    }
}

ARRAY_RANGE.setPattern(
    apply(seq(VAR_SYM, kmid(str('['), seq(TERM, kright(str('..'), TERM)), str(')'))), applyArrayRange)
)

function applyArrayElem(value: [AST.Variable, AST.Term]): AST.ArrayElem {
    return {
        isArrayElem: true, isArraySlice: true, isTerm: true,
        ident: value[0],
        idx: value[1],
        
    }
}

ARRAY_ELEM.setPattern(
    apply(seq(VAR_SYM, kmid(str('['), TERM, str(']'))), applyArrayElem)
)


function evaluate(line: string): AST.ASTNode {
    return expectSingleResult(expectEOF(PROOF_LINE.parse(lexer.parse(line))));
}