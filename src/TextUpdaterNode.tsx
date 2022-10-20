import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { Box, Heading, Button, Text, IconButton, useDisclosure } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverFooter,
  PopoverArrow,
  PopoverCloseButton,
  PopoverAnchor,
} from '@chakra-ui/react';
import { AddIcon } from '@chakra-ui/icons';

function TextUpdaterNode({ data }: any) {
  const onChange = useCallback((evt: any, updated: number) => {
    data.updateStatements(`${data.id}`, updated, evt.target.value);
  }, [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const firstProofStep: any = data.statements.findIndex((s: any) => !s.isGiven);
  const lastProofStep: any = data.statements.findLastIndex((s: any) => !s.isGiven);
  const checkSyntaxButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.checkSyntax(`${data.id}`) }}>Check Syntax</Button>;
  const deletePopover = 
    <Popover isOpen={isOpen} onClose={onClose}>
      <PopoverTrigger>
        <Button size='xs' colorScheme='blackAlpha' onClick={onOpen}>Delete</Button>
      </PopoverTrigger>
      <PopoverContent>
        <PopoverArrow />
        <PopoverCloseButton />
        <PopoverHeader>Are you sure you want to delete?</PopoverHeader>
        <PopoverBody style={{display: 'flex', justifyContent: 'space-between'}}>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.delete(`${data.id}`) }}>Yes, I'm sure!</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>

  if (data.type === "given") {
    return (
      <Box className={componentStyle}>
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
          {data.statements.map((s: any, index: number) => !s.isGiven && <input onChange={e => onChange(e, index)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {checkSyntaxButton}
        </div>
        {sourceHandle}
      </Box>
    )
  }


  if (data.type === "goal") {
    return (
      <Box className={componentStyle}>
        {targetHandle}
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
          {data.statements.map((s: any, index: number) => !s.isGiven && <input onChange={e => onChange(e, index)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {checkSyntaxButton}
        </div>
      </Box>
    )
  }

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
          {deletePopover}
          {data.statements.filter((s: any) => !s.isGiven).length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
          {checkSyntaxButton}
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
