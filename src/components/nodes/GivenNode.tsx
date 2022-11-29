import { Box, Button } from "@chakra-ui/react";
import { Handle, NodeProps, Position } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { NodeHandle } from "./NodeHandle";

export default function GivenNode({ data }: NodeProps<StatementNodeData>) {
  return (
    <Box className="given-node">
      
      <StatementList
        title="Givens"
        statements={data.goals}
        callbacks={data.thisNode.goals}
        afterStatementEdit={data.thisNode.checkSyntax}
      />

      {/* BEGIN : Delete Node Popover */}
      <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
        <DeleteNodePopover deleteNode={data.thisNode.delete} />
      </div>
      {/* END : Delete Node Popover */}

      
      {/* BEGIN : Bottom Handle */}
      <NodeHandle type="source"/>
      {/* END : Bottom Handle */}
    </Box>
  )
}
