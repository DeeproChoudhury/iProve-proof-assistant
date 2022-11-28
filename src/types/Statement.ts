import { Assumption, BeginScope, Line, VariableDeclaration } from "./AST";
import { Reason } from "./Reason";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
  reason?: Reason;
  wrappers: (VariableDeclaration | Assumption | BeginScope)[];
};

