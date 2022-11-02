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
import { ASTSMTLIB2, Line } from './AST';
import SolveNodeModal from './SolveNodeModal';

export type NodeType = "statement" | "given" | "goal";

export type StatementType = {
  value: string;
  syntaxCorrect?: boolean;
  parsed?: Line;
};

export type StatementKind = "given" | "proofStep" | "goal";

export type NodeData = Readonly<{
  label: string;
  id: number;
  type: NodeType;
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  correctImplication?: boolean;
  deleteNode: (nodeId: string) => void;
  updateStatement: (nodeId: string, k: StatementKind, statementIndex: number, statement: string) => void;
  addStatement: (nodeId: string, k: StatementKind) => void;
  addStatementAtIndex: (nodeId: string, k: StatementKind, index: number) => void;
  deleteStatementAtIndex: (nodeId: string, k: StatementKind, index: number) => void;
  checkSyntax: (nodeId: string) => void;
  checkEdges: (nodeId: string) => void;
}>;

export type StatementListFieldName = "givens" | "proofSteps" | "goals";

export function listField(k: StatementKind): StatementListFieldName {
    switch (k) {
        case "given": return "givens";
        case "proofStep": return "proofSteps";
        case "goal": return "goals";
    }
}

function TextUpdaterNode({ data }: { data: NodeData }) {
  const onChange = useCallback((evt: any, k: StatementKind, updated: number) => {
    data.updateStatement(`${data.id}`, k, updated, evt.target.value);
  }, [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();
  const { isOpen: isSolveNotReadyOpen, onOpen: onSolveNotReadyOpen, onClose: onSolveNotReadyClose } = useDisclosure();
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
        console.log(data.proofSteps);
        console.log(data.proofSteps.map(x => {
          return ASTSMTLIB2(x.parsed);
        }).join(" "));

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
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.deleteNode(`${data.id}`) }}>Yes, I'm sure!</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>
    
  const checkSolveReady = data.givens.concat(data.proofSteps, data.goals).every((s) => s.parsed !== undefined);
  const solveNotReadyPopover =
    <Popover isOpen={isSolveNotReadyOpen} onClose={onSolveNotReadyClose}>
      <PopoverTrigger>
        <Button size='xs' colorScheme='blackAlpha' onClick={onSolveNotReadyOpen}>Solve</Button>
      </PopoverTrigger>
      <PopoverContent>
        <PopoverArrow />
        <PopoverCloseButton />
        <PopoverHeader>Check node syntax first</PopoverHeader>
      </PopoverContent>
    </Popover>

  if (data.type === "given") {
    return (
      <Box className={componentStyle}>
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
          {data.givens.map((s: StatementType, index: number) =>
            <Statement onChange={e => onChange(e, "given", index)} statement={s} index={index} />)}
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
            <Statement onChange={e => onChange(e, "given", index)} statement={s} index={index} />)}
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
          onClick={() => { data.addStatement(`${data.id}`, "given") }}
          icon={<AddIcon />}
        />
      </div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {data.givens.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, "given", index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { data.addStatementAtIndex(`${data.id}`, "given", index) }}
            addBelow={() => { data.addStatementAtIndex(`${data.id}`, "given", index + 1) }} 
            deleteStatement = {() => {data.deleteStatementAtIndex(`${data.id}`, "given", index)}}/>)}
      </div>
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
        <Text>Proof Steps</Text>
        <IconButton
          variant='outline'
          aria-label='Add proof step'
          size='xs'
          onClick={() => { data.addStatement(`${data.id}`, "proofStep") }}
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
                onChange={e => onChange(e, "proofStep", 0)}
                statement={data.proofSteps[0]}
                index={data.givens.length}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", 0) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", 1) }}
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, "proofStep", 0) }} />
              <Text as='b'>. . .</Text>
              <Statement
                onChange={e => onChange(e, "proofStep", data.proofSteps.length - 1)}
                statement={data.proofSteps[data.proofSteps.length - 1]}
                index={data.givens.length + data.proofSteps.length - 1}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", data.proofSteps.length - 1) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", data.proofSteps.length) }} 
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, "proofStep", data.proofSteps.length - 1) }}/>
            </> :
            data.proofSteps.map((s: StatementType, index: number) =>
              <Statement
                onChange={e => onChange(e, "proofStep", index)}
                statement={s}
                index={data.givens.length + index}
                proofNode={true}
                addAbove={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", index) }}
                addBelow={() => { data.addStatementAtIndex(`${data.id}`, "proofStep", index + 1) }} 
                deleteStatement={() => { data.deleteStatementAtIndex(`${data.id}`, "proofStep", index) }} />)
        }
        <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
          <Text>Goals</Text>
          <IconButton
            variant='outline'
            aria-label='Add goal'
            size='xs'
            onClick={() => { data.addStatement(`${data.id}`, "goal") }}
            icon={<AddIcon />}
          />
        </div>
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          {data.goals.map((s: StatementType, index: number) =>
            <Statement
              onChange={e => onChange(e, "goal", index)}
              statement={s}
              index={data.givens.length + data.proofSteps.length + index}
              proofNode={true}
              addAbove={() => { data.addStatementAtIndex(`${data.id}`, "goal", index) }}
              addBelow={() => { data.addStatementAtIndex(`${data.id}`, "goal", index + 1) }} 
              deleteStatement = {() => {data.deleteStatementAtIndex(`${data.id}`, "goal", index)}}/>)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {data.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
          {checkSyntaxButton}
          {checkSolveReady ? checkSatButton : solveNotReadyPopover}
        </div>
      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
