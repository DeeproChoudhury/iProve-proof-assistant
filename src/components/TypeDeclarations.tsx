import { Box } from "@chakra-ui/react";
import './TypeDeclarations.css';
import StatementList from "./StatementList";
import { useIProveStore } from "../store/store";


const TypeDeclarations = () => {
  const typeDeclarations = useIProveStore(store => store.typeDeclarations);
  const actions = useIProveStore(store => store.actions.typeDeclarations);

  return (
    <Box className={"types"} >
      <StatementList
        title="Types"
        statements={typeDeclarations}
        callbacks={actions}
        isScrollable={true}
        afterStatementEdit={actions.parseAll}
      />
    </Box>
  )
}

export default TypeDeclarations;
