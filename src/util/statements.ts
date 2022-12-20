import { Line, Term } from "../types/AST";
import evaluate from "../logic/Parser";
import { StatementType } from "../types/Statement";
import { Setter } from "./setters";
import { IProveError } from "../types/ErrorLocation";
import { mk_error } from "./errors";
import { isTerm, toWrapperFunc } from "./trees";

export const updateWithParsed = (setError: (err: IProveError | undefined) => void) => (statement: StatementType) => {
  const parsedOrError = evaluate(statement.value);
  if(parsedOrError.kind === "Error") {
    statement.syntaxCorrect = false;
    setError(mk_error({
      kind: "Syntax", statement: statement, column: parsedOrError.pos?.columnBegin,
      msg: parsedOrError.message
        .replace("token: <END-OF-FILE>", "entire input")
    }));
  } else {
    // console.log(parsedOrError);
    statement.parsed = parsedOrError as Line; // TODO: avoid cast here?
    statement.syntaxCorrect = true;
  }
  return statement;
}

export const statementToLine = (statement: StatementType): Line | undefined => {
  if (!statement.parsed) return undefined;
  else if (isTerm(statement.parsed)) 
    return statement.wrappers.map(toWrapperFunc).reduceRight((accTerm, wrapperFunc) => wrapperFunc(accTerm), statement.parsed);
  else return statement.parsed;
}

export const unwrap_statements = (statements: StatementType[]): Line[] => {
  return statements.map(statementToLine).filter((line): line is Line => !!line);
}
