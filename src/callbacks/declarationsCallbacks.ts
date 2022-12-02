import { LI } from "../logic/LogicInterface";
import { Line, TypeDef } from "../types/AST";
import { IProveError } from"../types/ErrorLocation";
import { StatementType } from "../types/Statement";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { makeStatementListCallbacks } from "./statementListCallbacks";

  export const makeDeclarationCallbacks = (kind: "declarations" | "typeDeclarations", setDeclarations: Setter<StatementType[]>, setError: Setter<IProveError | undefined>) => ({
    ...makeStatementListCallbacks(setDeclarations, setError),
    checkSyntax: () => {
      setError(undefined)
      setDeclarations(decls => {
        const newDecls = decls.map(updateWithParsed(setError))
        const lines = newDecls.filter(s => s.parsed).map(s => s.parsed) as Line[];
        if (kind === "declarations") LI.setDeclarations(lines);
        else if (kind === "typeDeclarations") LI.setTypes(lines as TypeDef[]); // TODO error handling
        return newDecls;
      });
    }
  });

  export type DeclarationCallbacks = ReturnType<typeof makeDeclarationCallbacks>;
