import { StatementType } from "./Statement"

export type IProveError = {
  kind: "Syntax" | "Semantic" | "Proof" | undefined,
  status: "success" | "error",
  msg?: string,
  subtype?: string,
  pos?: ErrorLocation
}

export type IProveSuccess = {
  msg?: string
}

export type ErrorLocation = {
  statement: StatementType,
  column?: number
}
