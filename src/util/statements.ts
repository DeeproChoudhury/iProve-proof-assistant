import { DeclarationLine, GivenLine, GoalLine, Line, ProofStepLine, TypeDeclarationLine } from "../types/AST";
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

export const isDeclarationLine = (line: Line): line is DeclarationLine => {
  switch (line.kind) {
    case "FunctionDeclaration":
    case "VariableDeclaration":
    case "FunctionDefinition":
      return true;
  }
  return false;
}

export const isTypeDeclarationLine = (line: Line): line is TypeDeclarationLine => {
  return line.kind === "TypeDef";
}

export const isGivenLine = (line: Line): line is GivenLine => {
  return isTerm(line);
}

export const isProofStepLine = (line: Line): line is ProofStepLine => {
  switch (line.kind) {
    case "Assumption":
    case "Skolemize":
    case "BeginScope":
    case "EndScope":
      return true;
  }
  return isTerm(line);
}

export const isGoalLine = (line: Line): line is GoalLine => {
  return isTerm(line);
}
