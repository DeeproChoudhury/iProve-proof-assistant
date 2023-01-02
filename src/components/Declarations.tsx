import { Box } from "@chakra-ui/react";
import './Declarations.css';
import StatementList from "./StatementList";
import { useIProveStore } from "../store/store";

const Declarations = () => {
  const declarations = useIProveStore(store => store.declarations);
  const actions = useIProveStore(store => store.actions.declarations);

  return (
    <Box className={"declarations"} style={{ resize: "horizontal", overflow: "auto", minWidth: "300px"}}>
      <StatementList
        title="Declarations"
        statements={declarations}
        callbacks={actions}
        isScrollable={true}
        afterStatementEdit={actions.parseAll}
      />
    </Box>
  )
}

export default Declarations;
