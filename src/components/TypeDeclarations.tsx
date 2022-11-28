import { Box, Button } from "@chakra-ui/react";
import { ReactNode } from "react";
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

  const checkSyntaxButton: ReactNode = 
    <Button size='xs' colorScheme='blackAlpha' onClick={() => { checkSyntax() }}>Check Syntax</Button>;
  return (
    <Box className={"types " + (visible ? 'closed' : 'open')}>
      <StatementList
        title="Types"
        statements={statements}
        callbacks={{add, update, remove}}
        isScrollable={true}
        afterStatementEdit={() => checkSyntax()}
      />
      {checkSyntaxButton}
    </Box>
  )
}

export default TypeDeclarations;
