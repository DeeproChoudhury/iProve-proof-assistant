import { Assumption, BeginScope, Line, VariableDeclaration } from "../parser/AST";
import { Reason } from "./Reason";

export type StatementKind = "given" | "proofStep" | "goal";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
  reason?: Reason;
  wrappers: (VariableDeclaration | Assumption | BeginScope)[];
};

