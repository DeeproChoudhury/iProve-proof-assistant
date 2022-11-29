import { Box } from "@chakra-ui/react";
import './TypeDeclarations.css';
import { StatementType } from "../types/Statement";
import StatementList from "./StatementList";
import { DeclarationCallbacks } from "../callbacks/declarationsCallbacks";

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
    </Box>
  )
}

export default TypeDeclarations;
