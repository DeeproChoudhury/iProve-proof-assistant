import Z3Solver from "../solver/Solver";
import { StatementNodeData } from "../types/Node";
import { CheckStatus, Z3Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { absoluteIndexToLocal } from "./nodes";
import { Setter } from "./setters";
import { statementToZ3 } from "./statements";
import { LogicInterface } from "../logic/LogicInterface";

export const z3Reason = (dependencies: number[]): Z3Reason => ({ kind: "Z3", dependencies, status: "unchecked" });

export const checkReason = (data: StatementNodeData, statement: StatementType, updateReasonStatus: (status: CheckStatus) => void, setCheckFailed: Setter<boolean> | Setter<boolean | undefined>) => {
  if (!statement.reason) return;
  const depStatements = statement.reason.dependencies.map(absIndex => {
    const [listField, relIndex] = absoluteIndexToLocal(data, absIndex);
    return data[listField][relIndex];
  });
  if (depStatements.some(s => !s.parsed)) {
    setCheckFailed(true);
    updateReasonStatus("invalid");
    return;
  }

  updateReasonStatus("checking");

  {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}
  const LI = new LogicInterface;

  // Add globals/givens to the LogicInterface state
  data.declarationsRef.current.forEach(
    (declaration: StatementType) => statementToZ3(declaration, LI, "global")
  );
  depStatements.forEach(
    (declaration: StatementType) => statementToZ3(declaration, LI, "global")
  );
  
  if (statementToZ3(statement, LI, "goal")) {
    (new Z3Solver.Z3Prover("")).solve(`${LI}`).then(output => {
      if (output === "unsat\n") {
        setCheckFailed(false);
        updateReasonStatus("valid");
      } else {
        setCheckFailed(true);
        updateReasonStatus("invalid");
      }
    });
  }

  setCheckFailed(true);
  updateReasonStatus("invalid");
  {/* END LOGIC INTERFACE CRITICAL REGION */}
}
