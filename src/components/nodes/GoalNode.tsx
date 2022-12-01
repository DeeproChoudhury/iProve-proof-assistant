import { Box, Button } from "@chakra-ui/react";
import { useState, useEffect, useCallback } from "react";
import Moveable from "react-moveable";
import { NodeProps } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import { makeRecheckCallback } from "../../util/nodes";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { MoveableHandles } from "./MoveableHandle";
import { NodeHandle } from "./NodeHandle";

export default function GoalNode({ id, data }: NodeProps<StatementNodeData>) {
  const afterStatementEdit = useCallback(makeRecheckCallback({ type: "goalNode", data }), [data]);

  const [target, setTarget] = useState<any>();

  useEffect(() => {
    return setTarget(document.querySelector(`#goal-node-${id}`)!);
  }, [id]);

  return (
    <div>
      <Box className="goal-node" id={`goal-node-${id}`}>

        {/* START : Top Handle */}
        <NodeHandle type="target" />
        {/* END : Top Handle */}

        <div style={{ display: 'flex', justifyContent: 'center' }}>
          {data.edgesStatus === "unchecked" &&
            <Button colorScheme='whatsapp' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check incoming implications
            </Button>}
          {data.edgesStatus === "valid" &&
            <Button colorScheme='whatsapp' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check passed. Check again?
            </Button>}
          {data.edgesStatus === "invalid" &&
            <Button colorScheme='red' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check failed. Check again?
            </Button>}
        </div>
        <StatementList
          title="Goals"
          statements={data.givens}
          callbacks={data.thisNode.givens}
          afterStatementEdit={(index) => afterStatementEdit("givens", index)}
        />
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <DeleteNodePopover deleteNode={data.thisNode.delete} />
          {/* <Button size='xs' colorScheme='blackAlpha' onClick={data.thisNode.checkSyntax}>Check Syntax</Button> */}
        </div>
      </Box>

      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <MoveableHandles target={target} />
      {/* END: Moveable component to allow horizontal resizing */}
    </div>
  )
}
