import { Box, Button } from "@chakra-ui/react";
import { useState, useEffect, useCallback } from "react";
import Moveable from "react-moveable";
import { NodeProps } from "reactflow";
import { useStatementNodeActions } from "../../store/hooks";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { MoveableHandles } from "./MoveableHandle";
import { NodeHandle } from "./NodeHandle";

export default function GoalNode({ id, data }: NodeProps<StatementNodeData>) {
  const actions = useStatementNodeActions(id);
  const afterStatementEdit = actions.recheck;
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
            <Button variant="outline" colorScheme='whatsapp' size='xs' onClick={() => { actions.checkEdges() }}>
              Check incoming implications
            </Button>}
          {data.edgesStatus === "valid" &&
            <Button variant="outline" colorScheme='whatsapp' size='xs' onClick={() => { actions.checkEdges() }}>
              Check passed. Check again?
            </Button>}
          {data.edgesStatus === "invalid" &&
            <Button variant="outline" colorScheme='red' size='xs' onClick={() => { actions.checkEdges() }}>
              Check failed. Check again?
            </Button>}
        </div>
        <StatementList
          title="Goals"
          statements={data.givens}
          callbacks={actions.givens}
          afterStatementEdit={(index) => afterStatementEdit("givens", index)}
        />
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <DeleteNodePopover deleteNode={actions.deleteNode} />
          {/* <Button size='xs' colorScheme='blackAlpha' onClick={actions.checkSyntax}>Check Syntax</Button> */}
        </div>
      </Box>

      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <MoveableHandles target={target} />
      {/* END: Moveable component to allow horizontal resizing */}
    </div>
  )
}
