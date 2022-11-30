import { Line, Term } from "../types/AST";
import evaluate from "../logic/Parser";
import { StatementType } from "../types/Statement";
import { Setter } from "./setters";
import { IProveError } from "../components/Flow";
import { mk_error } from "./nodes";

export const updateWithParsed = (setError: Setter<IProveError | undefined>) => (statement: StatementType) => {
  const parsedOrError = evaluate(statement.value);
  if(parsedOrError.kind === "Error") {
    statement.syntaxCorrect = false;
    setError(mk_error({
      kind: "Syntax", statement: statement, column: parsedOrError.pos?.columnBegin,
      msg: parsedOrError.message
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
  for (let s of S) { if (s.parsed) R.push(s.parsed); }
  return R;
}
