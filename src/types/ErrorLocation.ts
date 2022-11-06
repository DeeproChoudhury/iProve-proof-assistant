import { StatementType } from "./Statement"

export type ErrorLocation = {
  statement: StatementType,
  column?: number
}