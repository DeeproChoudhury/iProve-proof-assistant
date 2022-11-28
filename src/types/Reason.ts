export type Reason = Z3Reason;

export type CheckStatus = "unchecked" | "checking" | "invalid" | "valid"

export type Z3Reason = { kind: "Z3", dependencies: number[], status: CheckStatus }
