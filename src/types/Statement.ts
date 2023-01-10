import { Assumption, BeginScope, Line, Skolemize, VariableDeclaration } from "./AST";
import { Reason } from "./Reason";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
  reason?: Reason;
  wrappers: (VariableDeclaration | Assumption | BeginScope | Skolemize)[];
};

