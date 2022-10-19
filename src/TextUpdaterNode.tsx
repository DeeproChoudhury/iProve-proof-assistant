import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { Box, Heading, Button, Text, IconButton } from '@chakra-ui/react';
import { AddIcon } from '@chakra-ui/icons';

function TextUpdaterNode({ data }: any) {
  const onChange = useCallback((evt: any, updated: number) => {
    data.updateStatements(`${data.id}`, updated, evt.target.value);
  }, []);

  const [isCollapsed, setCollapsed] = useState(false);

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const firstProofStep: any = data.statements.findIndex((s: any) => !s.isGiven);
  const lastProofStep: any = data.statements.findLastIndex((s: any) => !s.isGiven);

  return (
    <Box className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
        <Text>Givens</Text>
        <IconButton
          variant='outline'
          aria-label='Add given'
          size='xs'
          onClick={() => { data.addGiven(`${data.id}`) }}
          icon={<AddIcon />}
        />
      </div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {data.statements.map((s: any, index: number) => s.isGiven && <input onChange={e => onChange(e, index)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
      </div>
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
        <Text>Proof Steps</Text>
        <IconButton
          variant='outline'
          aria-label='Add proof step'
          size='xs'
          onClick={() => { data.addProofStep(`${data.id}`) }}
          icon={<AddIcon />}
        />
      </div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {componentStyle === "given-node" && givenTitle}
        {componentStyle === "goal-node" && goalTitle}
        {
          isCollapsed ?
            <>
              <input onChange={e => onChange(e, firstProofStep)} style={{ marginTop: '5px' }} key={firstProofStep} value={data.statements[firstProofStep].value} />
              <Text as='b'>. . .</Text>
              <input onChange={e => onChange(e, lastProofStep)} style={{ marginTop: '5px' }} key={lastProofStep} value={data.statements[lastProofStep].value} />
            </> :
            data.statements.map((s: any, index: number) => !s.isGiven && <input onChange={e => onChange(e, index)} style={{ marginTop: '5px' }} key={index} value={s.value} />)
        }
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.delete(`${data.id}`) }}>Delete</Button>
          {data.statements.filter((s: any) => !s.isGiven).length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
