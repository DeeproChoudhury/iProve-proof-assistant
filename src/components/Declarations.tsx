import { Box } from "@chakra-ui/react";
import './Declarations.css';
import { StatementType } from "../types/Statement";
import { DeclarationCallbacks } from "../callbacks/declarationsCallbacks";
import StatementList from "./StatementList";

export type DeclarationsPropsType = DeclarationCallbacks & {
  statements: StatementType[];
}

const Declarations = (props: DeclarationsPropsType) => {
  const { statements, add, update, remove, checkSyntax } = props;
  return (
    <Box className={"declarations"}>
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
