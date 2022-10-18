import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { Box, Heading, Button, Text} from '@chakra-ui/react';


function TextUpdaterNode({ data }: any) {
  const onChange = useCallback((evt: any, updated: number) => {
    data.updateStatements(`${data.id}`, updated, evt.target.value);
  }, []);

  const [isCollapsed, setCollapsed] = useState(false);
  
  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" />;
  const givenTitle: ReactNode = <Heading textAlign={['center' ]} as='h6' size='xs'>Given</Heading>
  const goalTitle : ReactNode = <Heading textAlign={['center' ]} as='h6' size='xs'>Goal</Heading>

  return (
    <Box className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <div style={{display: 'flex', flexDirection: 'column'}}>
        {componentStyle === "given-node" && givenTitle}
        {componentStyle === "goal-node" && goalTitle}
        {!isCollapsed && data.statements.map((s: string, index: number) => <input onChange={e => onChange(e, index)} style={{marginTop: '5px'}} key={index} value={s}/>)}
        {isCollapsed && [data.statements[0]].map((s: string, index: number) => <input onChange={e => onChange(e, index)} style={{marginTop: '5px'}} key={index} value={s}/>)}
        {isCollapsed && <Text as='b'>. . .</Text>}
        {isCollapsed && [data.statements[data.statements.length - 1]].map((s: string, index: number) => <input onChange={e => onChange(e, index)} style={{marginTop: '5px'}} key={index} value={s}/>)}

        <div style={{display: 'flex', justifyContent : 'space-between', marginTop: '5px'}}>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {data.delete(`${data.id}`)}}>Delete</Button>
          {data.statements.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => {setCollapsed(false)}}>Show</Button>}
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {data.addStatement(`${data.id}`)}}>Add Statement</Button>
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
