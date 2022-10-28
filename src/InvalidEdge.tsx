import { Button } from '@chakra-ui/react';
import React from 'react';
import { getBezierPath } from 'reactflow';
import './InvalidEdge.css';

const foreignObjectSize = 85;

export default function InvalidEdge({
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
        style={{stroke: "red"}}
        markerEnd={markerEnd}
      />
      <foreignObject
        width={foreignObjectSize}
        height={foreignObjectSize}
        x={labelX - foreignObjectSize / 2}
        y={labelY - foreignObjectSize / 2}
        className="invalid-edgebutton-foreignobject"
        requiredExtensions="http://www.w3.org/1999/xhtml"
      >
        <div>
          <Button colorScheme='red' size='xs' className='invalid-edgebutton' onClick={() => {data.onCheckEdge(id)}}>
            Check again
          </Button>
        </div>
      </foreignObject>
    </>
  );
}
