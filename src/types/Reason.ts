export type Reason = Z3Reason | SyntacticReason;

export type CheckStatus = "unchecked" | "invalid" | "valid"

export type Z3Reason = { kind: "Z3", dependencies: number[] }

export type SyntacticReason = { kind: "syntactic", dependencies: number[], rule: string };
