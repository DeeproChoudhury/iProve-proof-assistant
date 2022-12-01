import { Box, Button } from "@chakra-ui/react";
import { useState, useEffect } from "react";
import Moveable from "react-moveable";
import { NodeProps } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { NodeHandle } from "./NodeHandle";

export default function GoalNode({ id, data }: NodeProps<StatementNodeData>) {
  const [target, setTarget] = useState<any>();
  const [frame] = useState<any>({
    translate: [0, 0],
  });
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
          afterStatementEdit={data.thisNode.parseAll}
        />
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <DeleteNodePopover deleteNode={data.thisNode.delete} />
          {/* <Button size='xs' colorScheme='blackAlpha' onClick={data.thisNode.checkSyntax}>Check Syntax</Button> */}
        </div>
      </Box>

      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <Moveable
        target={target}
        resizable={true}
        keepRatio={false}
        throttleResize={1}
        renderDirections={["e", "w"]}
        edge={false}
        zoom={1}
        origin={false}
        padding={{ "left": 0, "top": 0, "right": 0, "bottom": 0 }}
        onResizeStart={e => {
          e.setOrigin(["%", "%"]);
          e.dragStart && e.dragStart.set(frame.translate);
        }}
        onResize={e => {
          const beforeTranslate = e.drag.beforeTranslate;
          frame.translate = beforeTranslate;
          e.target.style.width = `${e.width}px`;
          e.target.style.transform = `translate(${beforeTranslate[0]}px, 0px)`;
        }}
      />
      {/* END: Moveable component to allow horizontal resizing */}
    </div>
  )
}
