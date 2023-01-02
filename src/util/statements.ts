import { Line } from "../types/AST";
import { StatementType } from "../types/Statement";
import { isTerm, toWrapperFunc } from "./trees";

export const statementToLine = (statement: StatementType): Line | undefined => {
  if (!statement.parsed) return undefined;
  else if (isTerm(statement.parsed)) 
    return statement.wrappers.map(toWrapperFunc).reduceRight((accTerm, wrapperFunc) => wrapperFunc(accTerm), statement.parsed);
  else return statement.parsed;
}

export const unwrap_statements = (statements: StatementType[]): Line[] => {
  return statements.map(statementToLine).filter((line): line is Line => !!line);
}
