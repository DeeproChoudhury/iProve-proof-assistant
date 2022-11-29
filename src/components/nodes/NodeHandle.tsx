import { Position, Handle, HandleType } from "reactflow";

export function NodeHandle(props : { type : HandleType }) {
    const componentStyle = "node-handle";
    return (
        <Handle 
            className={componentStyle} 
            type={ props.type } 
            position={ props.type === "source" ? Position.Bottom : Position.Top } 
            style={{
                height: '12px',
                width: '12px',
                color: "green"
            }}
        />
    );
}
  
  