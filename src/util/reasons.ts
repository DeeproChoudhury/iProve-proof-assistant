import { isTerm, Line } from "../parser/AST";
import Z3Solver from "../solver/Solver";
import { StatementNodeData } from "../types/Node";
import { CheckStatus, Z3Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { absoluteIndexToLocal } from "./nodes";
import { Setter } from "./setters";
import { statementToZ3 } from "./statements";

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
  const depSMTs = depStatements.map(stat => {
    const smtStr = statementToZ3(stat);
    if (!stat.parsed) return "";
    if (isTerm(stat.parsed)) return `(assert ${smtStr})`;
    else return smtStr;
  });
  const concSMT = `(assert (not ${statementToZ3(statement)}))`;
  const z3Input = data.declarationsRef.current.map(statementToZ3).concat(depSMTs, [concSMT]).join("\n") + "\n(check-sat)";
  (new Z3Solver.Z3Prover("")).solve(z3Input).then(output => {
    if (output === "unsat\n") {
      setCheckFailed(false);
      updateReasonStatus("valid");
    } else {
      setCheckFailed(true);
      updateReasonStatus("invalid");
    }
  });
  
}
