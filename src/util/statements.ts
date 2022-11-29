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

export const statementToZ3 = (statement: StatementType, LI: LogicInterface, kind: "given" | "global" |"goal"): boolean => {
  if (!statement.parsed) return false;
  
  let st: Line = statement.parsed
  let toRender: Line = (isTerm(st))
    ? statement.wrappers
      .map(toWrapperFunc)
      .reduceRight(
        (accTerm: Term, wrapperFunc): Term => wrapperFunc(accTerm),
        st)
    : st

  switch (toRender.kind) {
    case "FunctionDeclaration":
      LI.addFnDecl(toRender); break;
    case "FunctionDefinition":
      LI.addFnDef(toRender); break;
    default: 
      switch (kind) {
        case "given": LI.addGiven(toRender); break;
        case "global": LI.addGlobal(toRender); break;
        case "goal":
          if (isTerm(toRender)) LI.setGoal(toRender);
          else return false
      }
  }

  return true;
}
