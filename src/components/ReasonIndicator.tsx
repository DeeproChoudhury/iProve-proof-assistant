import { CheckIcon, QuestionIcon, SpinnerIcon, WarningIcon } from "@chakra-ui/icons"
import { Tooltip } from "@chakra-ui/react";
import { Reason } from "../types/Reason"

export default function ReasonIndicator({ reason }: { reason: Reason }) {
  const [prefix, ReasonIcon] = {
    unchecked: ["[UNCHECKED] ", QuestionIcon],
    checking: ["[CHECKING] ", SpinnerIcon],
    invalid: ["[INVALID] ", WarningIcon],
    valid: ["", CheckIcon]
  }[reason.status];
  const label = prefix + (reason.dependencies.length === 0 ? 'lemma' : `from ${reason.dependencies.map(r => `(${r + 1})`).join(", ")}`)
  
  return <Tooltip label={label} fontSize='xs'>
    <ReasonIcon style={{margin: 'auto 5px'}}/>
  </Tooltip>
}
