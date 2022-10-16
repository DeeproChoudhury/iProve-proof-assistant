import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';

function TextUpdaterNode({ data }: any) {
  const [statements, setStatements] = useState<string[] | []>([]);

  const onChange = useCallback((evt: any, updated: number) => {
    statements[updated] = evt.target.value;
    setStatements(statements);
  }, [statements]);

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" />;

  return (
    <div className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <div style={{display: 'flex', flexDirection: 'column'}}>
        {statements.map((s, index) => <input onChange={e => onChange(e, index)} style={{marginTop: '5px'}} key={index}/>)}
        <div style={{display: 'flex', justifyContent : 'space-between', marginTop: '5px'}}>
          <button onClick={() => {data.delete(`${data.id}`)}}>Delete</button>
          <button onClick={() => {setStatements([...statements, ''])}}>Add Statement</button>
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </div>
  );
}

export default TextUpdaterNode;
