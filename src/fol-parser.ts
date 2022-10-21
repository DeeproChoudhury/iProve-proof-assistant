import { Token } from 'typescript-parsec';
import { buildLexer, expectEOF, expectSingleResult, rule } from 'typescript-parsec';
import { alt, apply, kmid, opt, seq, str, tok, kright, kleft, list_sc, lrec_sc } from 'typescript-parsec';
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
}

const lexer = buildLexer([
    [true, /^(FA|EX)/g, TokenKind.QntToken],
    [true, /^(\.\.)/g, TokenKind.DoubleDot],
    [true, /^(\:\:)/g, TokenKind.DoubleColon],
    [true, /^(var)/g, TokenKind.VarToken],
    [true, /^\d+/g, TokenKind.NumberLiteral],
    [true, /^\w+/g, TokenKind.Symbol],
    [true, /^((\-\>)|(\<\-\>))/g, TokenKind.ImpOperator],
    [true, /^(\+|\-|\=|\>|\<|\/|\.|\*|\!)+/g, TokenKind.InfixSymbol],
    [true, /^\~/g, TokenKind.NegToken],
    [true, /^(\&|\|)/g, TokenKind.PropOperator],
    [true, /^\S/g, TokenKind.Misc],
    [false, /^\s+/g, TokenKind.Space]
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

function applyIntLiteral(value: [Token<TokenKind> | undefined, Token<TokenKind.NumberLiteral>]): AST.IntLiteral {
    return {
        isIntLiteral: true, isAtom: true,
        n: parseInt(value[1].text) * (value[0] ? -1 : 1)
    }
}

function applyFnDeclaration(value: [AST.FunctionSymbol, AST.FunctionType]): AST.FunctionDeclaration {
    return {
        isDeclaration: true, isFunctionDeclaration: true,
        symbol: value[0],
        type: value[1]
    }
}

function applyVarDeclaration(value: [AST.Variable, AST.Type | undefined]): AST.VariableDeclaration {
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
const QUANTIFIED_FORMULA = rule<TokenKind, AST.QuantifiedFormula>();
const CLAUSE = rule<TokenKind, AST.Clause>();
const PROP_ATOM = rule<TokenKind, AST.PropAtom>();
const PROP_OPERATOR = rule<TokenKind, AST.PropOperator>();
const IMP_OPERATOR = rule<TokenKind, AST.ImpOperator>();
const COMPARISON = rule<TokenKind, AST.Comparison>();
const PREDICATE_FORMULA = rule<TokenKind, AST.Predicate>();
const TERM = rule<TokenKind, AST.Term>();
const ATOM = rule<TokenKind, AST.Atom>();



const TERM_LIST = rule<TokenKind, Array<AST.Term>>();
const V_L_ELEM = rule<TokenKind, AST.VLElem>();
const VAR_LIST = rule<TokenKind, Array<AST.VLElem>>();
const FUNCTION_APPLICATION = rule<TokenKind, AST.Function>();
const ARRAY_RANGE = rule<TokenKind, AST.ArrayRange>();
const ARRAY_ELEM = rule<TokenKind, AST.ArrayElem>();

const VAR_SYM = rule<TokenKind, AST.Variable>();
const FN_SYM = rule<TokenKind, AST.FunctionSymbol>();
const PREDICATE_SYM = rule<TokenKind, AST.PredicateSymbol>();
const INFIX_SYM = rule<TokenKind, AST.InfixSymbol>();
const VAR_TYPE = rule<TokenKind, AST.Type>();
const INT_LITERAL = rule<TokenKind, AST.IntLiteral>();

VAR_SYM.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Variable => {
    return { isSymbol: true, isAtom: true, isVariable: true, ident: s.text }
}));
FN_SYM.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.FunctionSymbol => {
    return { isSymbol: true, isFunctionSymbol: true, isInfixOperator: true, ident: s.text }
}));
PREDICATE_SYM.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.PredicateSymbol => {
    return { isSymbol: true, isPredicateSymbol: true, ident: s.text }
}));
VAR_TYPE.setPattern(apply(tok(TokenKind.Symbol), (s: Token<TokenKind.Symbol>): AST.Type => {
    return { isSymbol: true, isType: true, ident: s.text }
}));
INFIX_SYM.setPattern(apply(tok(TokenKind.InfixSymbol), (s: Token<TokenKind.InfixSymbol>): AST.InfixSymbol => {
    return { isInfixOperator: true, isInfixSymbol: true, ident: s.text }
}));
PROP_OPERATOR.setPattern(apply(tok(TokenKind.PropOperator), (s: Token<TokenKind.PropOperator>): AST.PropOperator => {
    return { isPropOperator: true, op: s.text }
}));
IMP_OPERATOR.setPattern(apply(tok(TokenKind.ImpOperator), (s: Token<TokenKind.ImpOperator>): AST.ImpOperator => {
    return { isImpOperator: true, op: s.text }
}));

INT_LITERAL.setPattern(
    apply(seq(opt(str('-')), tok(TokenKind.NumberLiteral)), applyIntLiteral)
)

PROOF_LINE.setPattern(
    alt(FORMULA, TYPE_EXT, TYPE_DEC)
)

TYPE_DEC.setPattern(
    alt(
        apply(seq(kleft(FN_SYM, str('::')), FN_TYPE), applyFnDeclaration),
        apply(seq(kright(opt(tok(TokenKind.VarToken)), VAR_SYM), opt(kright(str(':'), VAR_TYPE))), applyVarDeclaration),
    )
)

TYPE_EXT.setPattern(
    apply(seq(VAR_TYPE, kright(str('\\subset'), VAR_TYPE)), applyTypeExt)
)

function applyFunctionType(value: [AST.Type, AST.Type]): AST.FunctionType {
    return {
        isFunctionType: true,
        A: value[0],
        B: value[1]
    }
}

FN_TYPE.setPattern(
    apply(seq(VAR_TYPE, kright(alt(str('->'), str('\\implies')), VAR_TYPE)),
        applyFunctionType)
)

function applyParenFormula(x: AST.Formula): AST.ParenFormula {
    return {
        isPropAtom: true, isParenFormula: true,
        A: x
    }
}

PROP_ATOM.setPattern(
    alt(
        apply(kmid(str('['), FORMULA, str(']')), applyParenFormula),
        QUANTIFIED_FORMULA,
        PROPOSITIONAL_SYMBOL,
        PREDICATE_FORMULA,
        COMPARISON
    )
)

function applyPropSym(value: Token<TokenKind>): AST.PropLiteral {
    return {
        isPropLiteral: true, isPropAtom: true,
        truth: value.text == '\\top',
    }
}

PROPOSITIONAL_SYMBOL.setPattern(
    apply(alt(str('\\top'), str('\\bot')), applyPropSym)
)

function applyNegation(value: AST.Formula): AST.Neg {
    return {
        isPropAtom: true, isNeg: true,
        A: value
    }
}

NEG_FORMULA.setPattern(
    apply(kright(alt(str('\\neg'), str('\~')), FORMULA), applyNegation)
)

function applyComparison(value: [AST.Term, AST.InfixSymbol, AST.Term]): AST.Comparison {
    return {
        isComparison: true, isPropAtom: true,
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
        isPropAtom: true, isPredicate: true,
        pred: value[0],
        terms: value[1],
    }
}

PREDICATE_FORMULA.setPattern(
    apply(seq(PREDICATE_SYM, kmid(str('('), TERM_LIST, str(')'))), applyPredicateFormula)
)

function applyClause(x: AST.QFClause, y: [AST.PropOperator, AST.PropAtom]): AST.QFClause {
    x.atoms.push(y[1]);
    x.operators.push(y[0]);
    return {
        isClause: true, isQFClause: true,
        atoms: x.atoms,
        operators: x.operators
    }
}

function applyAtomicClause(x: AST.PropAtom): AST.QFClause {
    return {
        isClause: true, isQFClause: true,
        atoms: [x],
        operators: []
    }
}

CLAUSE.setPattern(
    lrec_sc(apply(PROP_ATOM, applyAtomicClause), seq(PROP_OPERATOR, PROP_ATOM), applyClause)
)

function applyQuantifiedFormula(value: [Token<TokenKind.QntToken>, Array<AST.VLElem>, AST.Clause]): AST.QuantifiedFormula {
    return {
        isPropAtom: true, isQuantifiedFormula: true,
        vars: value[1],
        quantifier: (value[0].text == "FA") ? AST.Quantifier.A : AST.Quantifier.E,
        A: value[2],
    }
}

QUANTIFIED_FORMULA.setPattern(
    apply(seq(tok(TokenKind.QntToken), kleft(VAR_LIST, str('.')), CLAUSE), applyQuantifiedFormula)
)

function applyFormula(x: AST.Formula, y: [AST.ImpOperator, AST.Clause]): AST.Formula {
    x.clauses.push(y[1]);
    x.operators.push(y[0]);
    return {
        isFormula: true,
        clauses: x.clauses,
        operators: x.operators
    }
}

function applyAtomicFormula(x: AST.Clause): AST.Formula {
    return {
        isFormula: true,
        clauses: [x],
        operators: []
    }
}

FORMULA.setPattern(
    lrec_sc(apply(CLAUSE, applyAtomicFormula), seq(IMP_OPERATOR, CLAUSE), applyFormula)
)

function applyTerm(x: AST.Term, y: [AST.InfixSymbol, AST.Atom]): AST.Term {
    x.atoms.push(y[1]);
    x.operators.push(y[0]);
    return {
        isTerm: true,
        atoms: x.atoms,
        operators: x.operators
    }
}


function applyAtomicTerm(x: AST.Atom): AST.Term {
    return {
        isTerm: true,
        atoms: [x],
        operators: []
    }
}

TERM.setPattern(
    lrec_sc(apply(ATOM, applyAtomicTerm), seq(INFIX_SYM, ATOM), applyTerm)
)

function applyParenTerm(x: AST.Term): AST.ParenTerm {
    return {
        isAtom: true, isParenTerm: true,
        x: x
    }
}

ATOM.setPattern(
    alt(
        apply(kmid(str('('), TERM, str(')')), applyParenTerm),
        FUNCTION_APPLICATION,
        ARRAY_RANGE,
        ARRAY_ELEM,
        VAR_SYM,
        INT_LITERAL
    )
)


TERM_LIST.setPattern(
    list_sc(TERM, str(','))
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
    list_sc(V_L_ELEM, str(','))
)

function applyFnApplication(value: [AST.FunctionSymbol, Array<AST.Term>]): AST.Function {
    return {
        isFunction: true, isAtom: true,
        fn: value[0],
        terms: value[1]
    }
}

FUNCTION_APPLICATION.setPattern(
    apply(seq(FN_SYM, kmid(str('('), TERM_LIST, str(')'))), applyFnApplication)
)


function applyArrayRange(value: [AST.Variable, [AST.Term, AST.Term]]): AST.ArrayRange {
    return {
        isArrayRange: true, isArraySlice: true, isAtom: true,
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
        isArrayElem: true, isArraySlice: true, isAtom: true,
        ident: value[0],
        idx: value[1],
        
    }
}

ARRAY_ELEM.setPattern(
    apply(seq(VAR_SYM, kmid(str('['), TERM, str(']'))), applyArrayElem)
)


export function evaluate(line: string): AST.ASTNode {
    return expectSingleResult(expectEOF(PROOF_LINE.parse(lexer.parse(line))));
}

export default evaluate;

const util = require('util');
let east = evaluate("var Gru");
console.log(util.inspect(east, {showHidden: false, depth: null, colors: true}));