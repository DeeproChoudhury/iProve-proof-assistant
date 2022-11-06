import { getBezierPath } from 'reactflow';
import './CheckedEdge.css';

export default function CheckedEdge({
  id,
  sourceX,
  sourceY,
  targetX,
  targetY,
  sourcePosition,
  targetPosition,
  style = {},
  data,
  markerEnd,
}: any) {
  const [edgePath, labelX, labelY] = getBezierPath({
    sourceX,
    sourceY,
    sourcePosition,
    targetX,
    targetY,
    targetPosition,
  });

  return (
    <>
      <path
        id={id}
        className="react-flow__edge-path"
        d={edgePath}
        style={{
          stroke: "green",
          strokeWidth: 5,
        }}
        markerEnd={markerEnd}
      />
    </>
  );
}
