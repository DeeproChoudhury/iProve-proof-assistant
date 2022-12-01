import { Line, Term } from "../types/AST";
import evaluate from "../logic/Parser";
import { StatementType } from "../types/Statement";
import { Setter } from "./setters";
import { IProveError } from "../types/ErrorLocation";
import { mk_error } from "./errors";

export const updateWithParsed = (setError: Setter<IProveError | undefined>) => (statement: StatementType) => {
  const parsedOrError = evaluate(statement.value);
  if(parsedOrError.kind === "Error") {
    statement.syntaxCorrect = false;
    setError(mk_error({
      kind: "Syntax", statement: statement, column: parsedOrError.pos?.columnBegin,
      msg: parsedOrError.message
        .replace("token: <END-OF-FILE>", "entire input")
    }));
  } else {
    console.log(parsedOrError);
    statement.parsed = parsedOrError as Line; // TODO: avoid cast here?
    statement.syntaxCorrect = true;
  }
  return statement;
}

export const unwrap_statements = (S: StatementType[]): Line[] => {
  let R: Line[] = []
  for (let s of S) { 
    if (s.parsed) {
      if (isTerm(s.parsed)) {
        R.push(s.wrappers.map(toWrapperFunc).reduceRight((accTerm, wrapperFunc) => wrapperFunc(accTerm), s.parsed));
      } else {
        R.push(s.parsed);
      }
    } 
  }
  return R;
}
