import { IProveError } from"../types/ErrorLocation";
import { StatementType } from "../types/Statement";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";

  export const makeDeclarationCallbacks = (setDeclarations: Setter<StatementType[]>, setError: Setter<IProveError | undefined>) => ({
    ...makeStatementListCallbacks(setDeclarations, setError),
    checkSyntax: () => {
      setError(undefined)
      setDeclarations(decls => decls.map(updateWithParsed(setError)))
    }
  });

  export type DeclarationCallbacks = ReturnType<typeof makeDeclarationCallbacks>;
