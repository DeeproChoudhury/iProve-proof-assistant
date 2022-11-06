import { Line } from "../parser/AST";
import { Reason } from "./Reason";

export type StatementKind = "given" | "proofStep" | "goal";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
  reason?: Reason;
};

