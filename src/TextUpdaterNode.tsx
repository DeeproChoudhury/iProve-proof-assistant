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
import Z3Solver from './Solver';

export type NodeType = "statement" | "given" | "goal";

export type Statement = {
  value: string;
};

export type NodeData = Readonly<{
  label: string;
  delete: (id: string) => void;
  id: number;
  type: NodeType;
  givens: Statement[];
  proofSteps: Statement[];
  updateGivens: (nodeId: string, statementIndex: number, statement: string) => void;
  updateProofSteps: (nodeId: string, statementIndex: number, statement: string) => void;
  addGiven: (nodeId: string) => void;
  addProofStep: (nodeId: string) => void;
  checkSyntax: (nodeId: string) => void;
}>;

function TextUpdaterNode({ data }: { data: NodeData }) {
  const onChange = useCallback((evt: any, updated: number, isGiven: boolean) => {
    if (isGiven) {
      data.updateGivens(`${data.id}`, updated, evt.target.value);
    } else {
      data.updateProofSteps(`${data.id}`, updated, evt.target.value);
    }
  }, [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();

  const localZ3Solver = new Z3Solver.Z3Prover("");

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const checkSyntaxButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.checkSyntax(`${data.id}`) }}>Check Syntax</Button>;
  const checkSatButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { localZ3Solver.solve("(declare-const x Int)\n(assert (not (= x x)))\n(check-sat)\n") }}>Solve</Button>;
  
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
          {data.givens.map((s: any, index: number) => <input onChange={e => onChange(e, index, true)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {checkSyntaxButton}
          {checkSatButton}
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
          {data.givens.map((s: any, index: number) => <input onChange={e => onChange(e, index, true)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {checkSyntaxButton}
          {checkSatButton}
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
        {data.givens.map((s: any, index: number) => <input onChange={e => onChange(e, index, true)} style={{ marginTop: '5px' }} key={index} value={s.value} />)}
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
              <input onChange={e => onChange(e, 0, false)} style={{ marginTop: '5px' }} value={data.proofSteps[0].value} />
              <Text as='b'>. . .</Text>
              <input onChange={e => onChange(e, data.proofSteps.length - 1, false)} style={{ marginTop: '5px' }} value={data.proofSteps[data.proofSteps.length - 1].value} />
            </> :
            data.proofSteps.map((s: any, index: number) => <input onChange={e => onChange(e, index, false)} style={{ marginTop: '5px' }} key={index} value={s.value} />)
        }
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {data.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
          {checkSyntaxButton}
          {checkSatButton}
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
