import { ErrorLocation } from "../types/ErrorLocation";
import { CheckStatus, Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";

export const makeStatementListCallbacks = (
  setStatements: Setter<StatementType[]>,
  setError: Setter<ErrorLocation | undefined>,
) => {
  return {
    add: (index?: number) => {
      setStatements(statements => {
        const result = [...statements];
        const newIndex = index ?? result.length
        result.splice(newIndex, 0, { value: "", wrappers: [] });
        return result;
      });
    },
    update: (index: number, statementValue: string) => {
      setStatements(statements => {
        const result = [...statements];
        result[index].value = statementValue;
        result[index].parsed = undefined;
        return result;
      });
    },
    remove: (index: number) => {
      setStatements(statements => {
        const result = [...statements];
        result.splice(index, 1);
        return result;
      });
    },
    parse: (index: number) => {
      setStatements(statements => {
        const result = [...statements];
        result[index] = updateWithParsed(setError)(result[index]);
        return result;
      })
    },
    parseAll: () => {
      setStatements(statements => statements.map(updateWithParsed(setError)));
    },
    addReason: (index: number, reason: Reason) => {
      setStatements(statements => {
        const result = [...statements];
        console.log(result, index);
        result[index].reason = reason;
        return result;
      });
    },
    removeReason: (index: number) => {
      setStatements(statements => {
        const result = [...statements];
        result[index].reason = undefined;
        return result;
      });
    },
    updateReasonStatus: (index: number, status: CheckStatus) => {
      setStatements(statements => {
        const result = [...statements];
        const reason = result[index].reason
        if (!reason) return statements;
        result[index].reason = {
          ...reason,
          status
        }
        return result;
      });
    },
    updateWithStatement: (index: number, statement: StatementType) => {
      setStatements(statements => {
        const result = [...statements];
        result[index] = statement;
        return result;
      });
    }
  }
};

export type StatementListCallbacks = ReturnType<typeof makeStatementListCallbacks>;
