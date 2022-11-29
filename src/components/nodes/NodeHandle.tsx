import { Box } from "@chakra-ui/react";
import { Position, Handle, HandleType } from "reactflow";

export function NodeHandle(props : { type : HandleType }) {
    return (
        <Handle  
            type={ props.type } 
            position={ props.type === "source" ? Position.Bottom : Position.Top } 
            className="custom-node-handle"
        />
    );
}
  
  