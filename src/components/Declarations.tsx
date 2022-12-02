import { Box } from "@chakra-ui/react";
import './Declarations.css';
import { StatementType } from "../types/Statement";
import { DeclarationCallbacks } from "../callbacks/declarationsCallbacks";
import StatementList from "./StatementList";
import InfoPopover from "./InfoPopover"


export type DeclarationsPropsType = DeclarationCallbacks & {
  statements: StatementType[];
  visible: boolean;
}

const Declarations = (props: DeclarationsPropsType) => {
  const { statements, add, update, remove, checkSyntax, visible } = props;
  return (
    <Box className={"declarations " + (visible ? 'closed' : 'open')}>
      <StatementList
        title="Declarations"
        statements={statements}
        callbacks={{add, update, remove}}
        isScrollable={true}
        afterStatementEdit={() => checkSyntax()}
      />
      <InfoPopover ml = "0px" title="Declarations Explanation" info="Please provide Haskell style 
      function types for all predicates used in the proof." />
    </Box>
  )
}

export default Declarations;
