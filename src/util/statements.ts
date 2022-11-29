import { Line, Term } from "../types/AST";
import evaluate from "../logic/Parser";
import { ErrorLocation } from "../types/ErrorLocation";
import { StatementType } from "../types/Statement";
import { Setter } from "./setters";
import { isTerm, toWrapperFunc } from "./trees";
import { LogicInterface } from "../logic/LogicInterface";

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

export const unwrap_statements = (S: StatementType[]): Line[] => {
  let R: Line[] = []
  for (let s of S) { if (s.parsed) R.push(s.parsed); }
  return R;
}
