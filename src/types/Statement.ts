import { Assumption, Line, VariableDeclaration } from "../parser/AST";
import { Reason } from "./Reason";

export type StatementKind = "given" | "proofStep" | "goal" | "type" | "baseCase" | "inductiveCase" | "predicate" | "inductiveHypothesis";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
  reason?: Reason;
  wrappers: (VariableDeclaration | Assumption)[];
};

