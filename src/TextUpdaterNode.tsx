import { ReactNode, useCallback } from 'react';
import { Handle, Position } from 'reactflow';

function TextUpdaterNode({ data }: any) {
  const onChange = useCallback((evt: any) => {
    console.log(evt.target.value);
  }, []);

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" />;

  return (
    <div className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <div>
        <input onChange={onChange} />
        <button onClick={() => {data.delete(`${data.id}`)}} style={{marginLeft: '5px'}}>Delete</button>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </div>
  );
}

export default TextUpdaterNode;
