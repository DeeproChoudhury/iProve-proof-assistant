import { Button } from '@chakra-ui/react';
import React from 'react';
import { getBezierPath } from 'reactflow';
import './ImplicationEdge.css';

const foreignObjectSize = 55;

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
        style={style}
        className="react-flow__edge-path"
        d={edgePath}
        markerEnd={markerEnd}
      />

      <foreignObject
        width={foreignObjectSize}
        height={foreignObjectSize}
        x={labelX - foreignObjectSize / 2}
        y={labelY - foreignObjectSize / 2}
        className="edgebutton-foreignobject"
        requiredExtensions="http://www.w3.org/1999/xhtml"
      >
        <div>
        <Button colorScheme='whatsapp' size='xs' className='edgebutton' onClick={() => {data.onCheckEdge(id)}}>
          Check
        </Button>
        </div>
      </foreignObject>
    </>
  );
}
