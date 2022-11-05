import { Button } from '@chakra-ui/react';
import React from 'react';
import { getBezierPath } from 'reactflow';
import './ImplicationEdge.css';

export default function ImplicationEdge({
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
        style={{
          stroke: "black",
          strokeWidth : 5
        }}
        className="react-flow__edge-path"
        d={edgePath}
        markerEnd={markerEnd}
      />
    </>
  );
}
