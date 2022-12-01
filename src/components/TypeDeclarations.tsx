import { Box } from "@chakra-ui/react";
import './TypeDeclarations.css';
import { StatementType } from "../types/Statement";
import StatementList from "./StatementList";
import { DeclarationCallbacks } from "../callbacks/declarationsCallbacks";
import InfoPopover from "./InfoPopover";

export type TypesPropsType = DeclarationCallbacks & {
  statements: StatementType[];
  visible: boolean;
}

const TypeDeclarations = (props: TypesPropsType) => {
  const { statements, update, add, remove, checkSyntax, visible } = props;
  return (
    <Box className={"types " + (visible ? 'closed' : 'open')}>
      <StatementList
        title="Types"
        statements={statements}
        callbacks={{add, update, remove}}
        isScrollable={true}
        afterStatementEdit={() => checkSyntax()}
      />
      <InfoPopover title="Types Explanation" info="Please define all custom types
      using Haskell style type defintions. Custom types can be 
      used in function declarations above!" />
    </Box>
  )
}

export default TypeDeclarations;
