import { Box } from "@chakra-ui/react";
import { useState, useEffect } from "react";
import { NodeProps } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { MoveableHandles } from "./MoveableHandle";
import { NodeHandle } from "./NodeHandle";

export default function GivenNode({ id, data }: NodeProps<StatementNodeData>) {
  const [target, setTarget] = useState<any>();
  
  useEffect(() => {
    return setTarget(document.querySelector(`#given-node-${id}`)!);
  }, [id]);
  return (
    <div>
      <Box className="given-node" id={`given-node-${id}`}>

        <StatementList
          title="Givens"
          statements={data.goals}
          callbacks={data.thisNode.goals}
          afterStatementEdit={data.thisNode.parseAll}
        />

        {/* BEGIN : Delete Node Popover */}
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <DeleteNodePopover deleteNode={data.thisNode.delete} />
        </div>
        {/* END : Delete Node Popover */}


        {/* BEGIN : Bottom Handle */}
        <NodeHandle type="source" />
        {/* END : Bottom Handle */}
      </Box>

      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <MoveableHandles target={target} />
      {/* END: Moveable component to allow horizontal resizing */}
    
    </div>
  )
}

