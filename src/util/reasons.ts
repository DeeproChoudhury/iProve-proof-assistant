import { StatementNodeData } from "../types/Node";
import { CheckStatus, Z3Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { absoluteIndexToLocal } from "./nodes";
import { Setter } from "./setters";
import { statementToLine, unwrap_statements } from "./statements";
import { LI, LogicInterface } from "../logic/LogicInterface";
import { IProveError } from  "../types/ErrorLocation";
import { mk_error, parse_error } from "./errors";
import { Line, TypeDef } from "../types/AST";
import { LIQ } from "../logic/LogicInterfaceQueue";

export const z3Reason = (dependencies: number[]): Z3Reason => ({ kind: "Z3", dependencies, status: "unchecked" });

export const checkReason = (data: StatementNodeData, statement: StatementType, updateReasonStatus: (status: CheckStatus) => void, setCheckFailed: Setter<IProveError | undefined>) => {
  if (!statement.reason) return;
  const depStatements = statement.reason.dependencies.map(absIndex => {
    const [listField, relIndex] = absoluteIndexToLocal(data, absIndex);
    return data[listField][relIndex];
  });
  if (depStatements.some(s => !s.parsed)) {
    setCheckFailed({
      kind: "Semantic",
      msg: "Some givens have not been parsed! Exit the modal and try again"
    });
    updateReasonStatus("invalid");
    data.thisNode.checkInternal();
    return;
  }

  updateReasonStatus("checking");

  if (!statement.parsed) {
    setCheckFailed({
      kind: "Semantic",
      msg: "Your objective has not been parsed! Exit the modal and try again"
    });
    updateReasonStatus("invalid");
  }
  LIQ.queueEntails(unwrap_statements(depStatements), statementToLine(statement) as Line, verdict => {
    switch (verdict.kind) {
      case "Valid":
        setCheckFailed(undefined);
        updateReasonStatus("valid");
        break;
      case "Error":
        setCheckFailed(parse_error(verdict));
        updateReasonStatus("invalid");
        break;
      case "Unknown":
        setCheckFailed(mk_error({
          msg: "We couldn't decide whether your conclusion was true. This is either because you haven't provided enough granularity in your proof, or because your conclusion doesn't hold; try deducing more intermediate steps and supplying those as reasons, or making your conclusion more specific to the case you are working on."
        }));
        updateReasonStatus("invalid");
        break;
      case "False":
        setCheckFailed({ kind: "Proof" });
        updateReasonStatus("invalid");
    }
    data.thisNode.checkInternal();
  });
}
