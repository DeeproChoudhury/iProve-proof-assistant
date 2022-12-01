import { alt, apply, buildLexer, expectSingleResult, kmid, kright, Lexer, opt, rep_sc, rule, seq, str, tok, Token } from "typescript-parsec"
import { IProveError } from "../types/ErrorLocation"
import { ProofOutcome } from "../logic/LogicInterface"
import { StatementType } from "../types/Statement"

export function renderError(E: IProveError): string {
    switch (E.kind) {
      case "Syntax": {
        let msg = E.msg ?? "Parsing for the last node failed"
        return E.pos?.column
          ? `${msg} - Detected at column ${E.pos.column}, in "${E.pos.statement.value}"`
          : `${msg} - Check your syntax!`
      }
      case "Proof":
        return E.pos?.statement
          ? `Validity check failed on statement ${E.pos.statement.value}, check your implications!`
          : `Validity check failed, check your implications!`
      case "Semantic":
        return E.pos?.statement
          ? `${E.subtype ?? "Error"} in ${E.pos.statement.value}: ${E.msg}`
          : (E.subtype ? `${E.subtype}: ${E.msg}` : (E.msg ?? ""))
      default:
        return E.msg ?? ""
    }
  }
  
export function mk_error({
kind = undefined,
msg = undefined,
subtype = undefined,
statement = undefined,
column = undefined
}:{
kind?: "Syntax" | "Semantic" | "Proof",
msg?: string,
subtype?: string,
statement?: StatementType,
column?: number
}): IProveError {
return {
    kind: kind,
    msg: msg,
    subtype: subtype,
    pos: (statement)
    ? { statement: statement, column: column}
    : undefined
}
}

type ErrorToken = ":" | '"' | "Word" | "Other" | "Space";
const error_lexer: Lexer<ErrorToken> = buildLexer([
[true, /^\:/g, ":"],
[true, /^\"/g, "\""],
[true, /^[^\"\s\:]+/g, "Word"],
[true, /^\S/g, "Other"],

[false, /^(\s|\n)+/g, "Space"]
]);

const STRING = rule<ErrorToken, string>()
const Z3_ERRORS = rule<ErrorToken, IProveError>()
STRING.setPattern(apply(rep_sc(tok("Word")),
    (v: Token<"Word">[]): string =>
    { return v.map((x) => x.text).join(" "); }
    ))

Z3_ERRORS.setPattern(
apply(
    kmid(
        tok("Word"),
        kmid(tok("\""), kright(opt(seq(STRING, tok(":"))), STRING), tok("\"")),
        str(")")
    ),
    (v: string)
    : IProveError => (mk_error({
        kind: "Semantic",
        msg: v,
    }))
)
)

export function parse_z3_error(e: string): IProveError | undefined {
    let A = Z3_ERRORS.parse(error_lexer.parse(e));
    if (!A.successful) return;
    return expectSingleResult(A);
}

export function parse_error(O: ProofOutcome): IProveError | undefined {
if (O.kind != "Error") return;
if (O.emitter == "IProve") return mk_error({
    kind: "Semantic",
    msg: O.msg
})
return parse_z3_error(O.msg)
}
