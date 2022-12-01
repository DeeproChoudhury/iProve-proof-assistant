import { Box } from "@chakra-ui/react";
import { useState, useEffect } from "react";
import Moveable from "react-moveable";
import { NodeProps } from "reactflow";
import { StatementNodeData } from "../../types/Node";
import StatementList from "../StatementList";
import { DeleteNodePopover } from "./GeneralNode";
import { NodeHandle } from "./NodeHandle";

export default function GivenNode({ id, data }: NodeProps<StatementNodeData>) {
  const [target, setTarget] = useState<any>();
  const [frame] = useState<any>({
    translate: [0, 0],
  });
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
