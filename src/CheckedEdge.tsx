import { Button } from '@chakra-ui/react';
import React from 'react';
import { getBezierPath } from 'reactflow';
import './CheckedEdge.css';

const foreignObjectSize = 55;

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
        style={{stroke: "green"}}
        markerEnd={markerEnd}
      />
    </>
  );
}
