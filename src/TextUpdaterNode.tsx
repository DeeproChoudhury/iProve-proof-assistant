import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { Box, Heading, Button, Text, IconButton, useDisclosure } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
} from '@chakra-ui/react';
import { AddIcon } from '@chakra-ui/icons';
import Z3Solver from './Solver';
import Statement from './Statement';
import { Line } from './AST';
import SolveNodeModal from './SolveNodeModal';

export type NodeType = "statement" | "given" | "goal";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
};

export enum ProofNodeTypes {
  GIVEN, 
  PROOFSTEP, 
  GOAL
}

export type NodeData = Readonly<{
  label: string;
  delete: (id: string) => void;
  id: number;
  type: NodeType;
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  correctImplication?: boolean;
  updateGivens: (nodeId: string, statementIndex: number, statement: string) => void;
  updateProofSteps: (nodeId: string, statementIndex: number, statement: string) => void;
  updateGoals: (nodeId: string, statementIndex: number, statement: string) => void;
  addGiven: (nodeId: string) => void;
  addProofStep: (nodeId: string) => void;
  addGoal: (nodeId: string) => void;
  addStatementAtIndex: (nodeId: string, index: number, t: ProofNodeTypes) => void;
  checkSyntax: (nodeId: string) => void;
  checkEdges: (nodeId: string) => void;
  deleteStatementAtIndex: (nodeId: string, index: number, t: ProofNodeTypes) => void;
}>;

function TextUpdaterNode({ data }: { data: NodeData }) {
  const onChange = useCallback((evt: any, updated: number, t: ProofNodeTypes) => {
    if (t === ProofNodeTypes.GIVEN) {
      data.updateGivens(`${data.id}`, updated, evt.target.value);
    } else if (t === ProofNodeTypes.PROOFSTEP) {
      data.updateProofSteps(`${data.id}`, updated, evt.target.value);
    } else {
      data.updateGoals(`${data.id}`, updated, evt.target.value);
    }
  }, [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();
  const { isOpen: isSolveModalOpen, onOpen: onSolveModalOpen, onClose: onSolveModalClose } = useDisclosure();

  const localZ3Solver = new Z3Solver.Z3Prover("");

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const checkSyntaxButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.checkSyntax(`${data.id}`) }}>Check Syntax</Button>;
  const checkSatButton: ReactNode = 
    <Button size='xs' 
      colorScheme='blackAlpha' 
      onClick={() => { 
        onSolveModalOpen();
        // console.log(isSolveModalOpen);
        localZ3Solver.solve("(declare-const x Int)\n(assert (not (= x x)))\n(check-sat)\n") 
      }}>
      Solve
    </Button>;
  
  const deletePopover =
    <Popover isOpen={isOpen} onClose={onClose}>
      <PopoverTrigger>
        <Button size='xs' colorScheme='blackAlpha' onClick={onOpen}>Delete</Button>
      </PopoverTrigger>
      <PopoverContent>
        <PopoverArrow />
        <PopoverCloseButton />
        <PopoverHeader>Are you sure you want to delete?</PopoverHeader>
        <PopoverBody style={{ display: 'flex', justifyContent: 'space-between' }}>
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
          {data.givens.map((s: StatementType, index: number) =>
            <Statement onChange={e => onChange(e, index, ProofNodeTypes.GIVEN)} statement={s} index={index} />)}
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
          {data.givens.map((s: StatementType, index: number) =>
            <Statement onChange={e => onChange(e, index, ProofNodeTypes.GIVEN)} statement={s} index={index} />)}
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
      <SolveNodeModal 
        isOpen={isSolveModalOpen} 
        onClose={onSolveModalClose} 
        node={data}/>
      <div style={{display: 'flex', justifyContent: 'center'}}>
      {data.correctImplication === undefined &&
      <Button colorScheme='whatsapp' size='xs' onClick={() => {data.checkEdges(`${data.id}`)}}>
        Check incoming implications
      </Button>}
      {data.correctImplication === true &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {data.checkEdges(`${data.id}`)}}>
          Check passed. Check again?
        </Button>}
      {data.correctImplication === false &&
        <Button colorScheme='red' size='xs' onClick={() => {data.checkEdges(`${data.id}`)}}>
          Check failed. Check again?
        </Button>}
      </div>
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
        {data.givens.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, index, ProofNodeTypes.GIVEN)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { data.addStatementAtIndex(`${data.id}`, index, ProofNodeTypes.GIVEN) }}
            addBelow={() => { data.addStatementAtIndex(`${data.id}`, index + 1, ProofNodeTypes.GIVEN) }} 
            deleteStatement = {() => {data.deleteStatementAtIndex(`${data.id}`, index, ProofNodeTypes.GIVEN)}}/>)}
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
              <Statement
                onChange={e => onChange(e, 0, ProofNodeTypes.PROOFSTEP)}
                statement={data.proofSteps[0]}
                index={data.givens.length}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, 0, ProofNodeTypes.PROOFSTEP) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, 1, ProofNodeTypes.PROOFSTEP) }}
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, 0, ProofNodeTypes.PROOFSTEP) }} />
              <Text as='b'>. . .</Text>
              <Statement
                onChange={e => onChange(e, data.proofSteps.length - 1, ProofNodeTypes.PROOFSTEP)}
                statement={data.proofSteps[data.proofSteps.length - 1]}
                index={data.givens.length + data.proofSteps.length - 1}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, data.proofSteps.length - 1, ProofNodeTypes.PROOFSTEP) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, data.proofSteps.length, ProofNodeTypes.PROOFSTEP) }} 
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, data.proofSteps.length - 1, ProofNodeTypes.PROOFSTEP) }}/>
            </> :
            data.proofSteps.map((s: StatementType, index: number) =>
              <Statement
                onChange={e => onChange(e, index, ProofNodeTypes.PROOFSTEP)}
                statement={s}
                index={data.givens.length + index}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, index, ProofNodeTypes.PROOFSTEP) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, index + 1, ProofNodeTypes.PROOFSTEP) }} 
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, index, ProofNodeTypes.PROOFSTEP) }} />)
        }
        <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
          <Text>Goals</Text>
          <IconButton
            variant='outline'
            aria-label='Add goal'
            size='xs'
            onClick={() => { data.addGoal(`${data.id}`) }}
            icon={<AddIcon />}
          />
        </div>
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          {data.goals.map((s: StatementType, index: number) =>
            <Statement
              onChange={e => onChange(e, index, ProofNodeTypes.GOAL)}
              statement={s}
              index={data.givens.length + data.proofSteps.length + index}
              proofNode={true}
              addAbove={() => { data.addStatementAtIndex(`${data.id}`, index, ProofNodeTypes.GOAL) }}
              addBelow={() => { data.addStatementAtIndex(`${data.id}`, index + 1, ProofNodeTypes.GOAL) }} 
              deleteStatement = {() => {data.deleteStatementAtIndex(`${data.id}`, index, ProofNodeTypes.GOAL)}}/>)}
        </div>
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
