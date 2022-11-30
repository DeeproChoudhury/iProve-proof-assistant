import Z3Solver from "../logic/Solver";
import { StatementNodeData } from "../types/Node";
import { CheckStatus, Z3Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { absoluteIndexToLocal } from "./nodes";
import { Setter } from "./setters";
import { unwrap_statements } from "./statements";
import { LI, LogicInterface } from "../logic/LogicInterface";
import { Line, Term } from "../types/AST";

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

  LI.setDeclarations(unwrap_statements(data.declarationsRef.current))
  if (statement.parsed)
    LI.entails(unwrap_statements(depStatements), statement.parsed).then(
      verdict => {
        console.log("RVERD", verdict)
        if (verdict.kind == "Valid") {
          setCheckFailed(false);
          updateReasonStatus("valid");
        } else {
          setCheckFailed(true);
          updateReasonStatus("invalid");
        }
      }
    );

  setCheckFailed(true);
  updateReasonStatus("invalid");
  
  {/* END LOGIC INTERFACE CRITICAL REGION */}
}
