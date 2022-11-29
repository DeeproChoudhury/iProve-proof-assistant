import { Box } from "@chakra-ui/react";
import './Declarations.css';
import { StatementType } from "../types/Statement";
import { DeclarationCallbacks } from "../callbacks/declarationsCallbacks";
import StatementList from "./StatementList";

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
    </Box>
  )
}

export default Declarations;
