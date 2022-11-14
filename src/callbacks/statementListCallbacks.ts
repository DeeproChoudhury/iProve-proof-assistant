import { Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { Setter } from "../util/setters";

export const makeStatementListCallbacks = (
  setStatements: Setter<StatementType[]>
) => {
  // const shiftReasons = (index: number, offset: number) => {
  //   setStatements(statements => statements.map((statement, i) => {
  //     if (i <= index) return statement;
  //     if (!statement.reason) return statement;
  //
  //     return {
  //       ...statement,
  //       reason: {
  //         ...statement.reason,
  //         dependencies: statement.reason.dependencies.map((j) => j <= index ? j : j + offset)
  //       }
  //     }
  //   }));
  //   chainShiftReasons?.(index, offset);
  // };
  //
  // const invalidateReason = (index: number, removed: number[]) => {
  //   setStatements(statements => statements.map((statement, i) => {
  //     console.log(`${i}`);
  //     if (i < index) return statement;
  //     if (i === index) return { ...statement, reason: undefined};
  //     if (!statement.reason) return statement;
  //     
  //     console.log(`checking whether ${i} depends on ${index}`)
  //     let newReason: Reason | undefined = statement.reason;
  //     console.dir(statement);
  //     console.log(removed);
  //     if (statement.reason.dependencies.some(x => removed.includes(x))) {
  //       console.log(`invalidating ${i}`);
  //       removed.push(i);
  //       newReason = undefined;
  //     }
  //     return { ...statement, reason: newReason };
  //   }));
  //   chainInvalidateReason?.(removed);
  // }
  
  return {
    add: (index?: number) => {
      setStatements(statements => {
        const result = [...statements];
        const newIndex = index ?? result.length
        result.splice(newIndex, 0, { value: "" });
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
    addReason: (index: number, reason: Reason) => {
      setStatements(statements => {
        const result = [...statements];
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
    }
  }
};

export type StatementListCallbacks = ReturnType<typeof makeStatementListCallbacks>;
