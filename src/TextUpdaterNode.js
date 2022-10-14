import { useCallback } from 'react';
import { Handle, Position } from 'reactflow';

function TextUpdaterNode({ data }) {
  const onChange = useCallback((evt) => {
    console.log(evt.target.value);
  }, []);

  const componentStyle = {
    statement: "text-updater-node",
    given: "given-node",
    goal: "goal-node",
  }[data.type];

  return (
    <div className={componentStyle}>
      {componentStyle !== "given-node" && <Handle type="target" position={Position.Top} />}
      <div>
        <input onChange={onChange} />
        <button onClick={() => {data.delete(`${data.id}`)}} style={{marginLeft: '5px'}}>Delete</button>
      </div>
      {componentStyle !== "goal-node" && <Handle type="source" position={Position.Bottom} id="b" />}
    </div>
  );
}

export default TextUpdaterNode;
