import { Z3Reason } from "../types/Reason";

export const z3Reason = (dependencies: number[]): Z3Reason => ({ kind: "Z3", dependencies });
