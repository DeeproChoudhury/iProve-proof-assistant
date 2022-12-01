import { useState } from "react";
import Moveable from "react-moveable";

/**
 * Component for resizing Nodes in the horizontal direction
 * 
 * @param target the target node to be resized
 *  */
export function MoveableHandles(props : {target: any}) {
    
    const [frame] = useState<any>({
        translate: [0, 0],
    });
    
    return (
    <Moveable
        target={props.target}
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
    )
}