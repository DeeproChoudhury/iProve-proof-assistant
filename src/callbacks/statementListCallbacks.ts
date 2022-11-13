import { Assumption, VariableDeclaration } from "../parser/AST";
import { Reason } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { Setter } from "../util/setters";

export const makeStatementListCallbacks = (setStatements: Setter<StatementType[]>) => ({
  add: (index?: number, wrappers: (VariableDeclaration | Assumption)[] = []) => setStatements(statements => {
    const result = [...statements];
    result.splice(index ?? result.length, 0, { value: "", wrappers: wrappers});
    return result;
  }),
  update: (index: number, statementValue: string) => setStatements(statements => {
    const result = [...statements];
    result[index].value = statementValue;
    result[index].parsed = undefined;
    return result;
  }),
  remove: (index: number) => setStatements(statements => {
    const result = [...statements];
    result.splice(index, 1);
    return result;
  }),
  addReason: (index: number, reason: Reason) => setStatements(statements => {
    const result = [...statements];
    result[index].reason = reason;
    return result;
  })
});

export type StatementListCallbacks = ReturnType<typeof makeStatementListCallbacks>;
