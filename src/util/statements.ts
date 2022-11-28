import { ASTSMTLIB2, isTerm, Line, toWrapperFunc } from "../parser/AST";
import evaluate from "../parser/fol-parser";
import { ErrorLocation } from "../types/ErrorLocation";
import { StatementType } from "../types/Statement";
import { Setter } from "./setters";

export const updateWithParsed = (setError: Setter<ErrorLocation | undefined>) => (statement: StatementType) => {
  const parsedOrError = evaluate(statement.value);
  if(parsedOrError.kind === "Error") {
    statement.syntaxCorrect = false;
    setError({statement, column: parsedOrError.pos?.columnBegin});
  } else {
    console.log(parsedOrError);
    statement.parsed = parsedOrError as Line; // TODO: avoid cast here?
    statement.syntaxCorrect = true;
  }
  return statement;
}

export const statementToZ3 = (statement: StatementType): string => {
  if (!statement.parsed) return "";
  else if (isTerm(statement.parsed)) return ASTSMTLIB2(statement.wrappers.map(toWrapperFunc).reduceRight((accTerm, wrapperFunc) => wrapperFunc(accTerm), statement.parsed)) ?? "";
  else return ASTSMTLIB2(statement.parsed);
}
