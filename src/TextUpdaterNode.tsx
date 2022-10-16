import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';

function TextUpdaterNode({ data }: any) {
  const onChange = useCallback((evt: any, updated: number) => {
    data.updateStatements(`${data.id}`, updated, evt.target.value);
  }, []);

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" />;
  return (
    <div className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <div style={{display: 'flex', flexDirection: 'column'}}>
        {data.statements.map((s: string, index: number) => <input onChange={e => onChange(e, index)} style={{marginTop: '5px'}} key={index} value={s}/>)}
        <div style={{display: 'flex', justifyContent : 'space-between', marginTop: '5px'}}>
          <button onClick={() => {data.delete(`${data.id}`)}}>Delete</button>
          <button onClick={() => {data.addStatement(`${data.id}`)}}>Add Statement</button>
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </div>
  );
}

export default TextUpdaterNode;
