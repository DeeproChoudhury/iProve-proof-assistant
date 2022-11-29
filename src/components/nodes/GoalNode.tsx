import { Box, Button } from "@chakra-ui/react";
import { Handle, NodeProps, Position } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { NodeHandle } from "./NodeHandle";

export default function GoalNode({ data }: NodeProps<StatementNodeData>) {
  return (
    <Box className="goal-node">
      
      {/* START : Top Handle */}
      <NodeHandle type="target" />
      {/* END : Top Handle */}

      <div style={{display: 'flex', justifyContent: 'center'}}>
      {data.correctImplication === undefined &&
      <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
        Check incoming implications
      </Button>}
      {data.correctImplication === "valid" &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check passed. Check again?
        </Button>}
      {data.correctImplication === "invalid" &&
        <Button colorScheme='red' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check failed. Check again?
        </Button>}
      </div>
      <StatementList
        title="Goals"
        statements={data.givens}
        callbacks={data.thisNode.givens}
        afterStatementEdit={data.thisNode.checkSyntax}
      />
      <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
        <DeleteNodePopover deleteNode={data.thisNode.delete} />
        {/* <Button size='xs' colorScheme='blackAlpha' onClick={data.thisNode.checkSyntax}>Check Syntax</Button> */}
      </div>
    </Box>
  )
}
