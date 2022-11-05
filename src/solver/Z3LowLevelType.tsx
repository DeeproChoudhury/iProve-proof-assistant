import { init } from "z3-solver"

export type Z3LowLevelType = Awaited<ReturnType<typeof init>>["Z3"];
