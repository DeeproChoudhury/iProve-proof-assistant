import { AddIcon } from '@chakra-ui/icons';
import {
  Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { NodeData } from '../types/Node';
import { StatementKind, StatementType } from '../types/Statement';
import { listField, localIndexToAbsolute } from '../util/nodes';
import SolveNodeModal from './SolveNodeModal';
import Statement from './Statement';

function TextUpdaterNode({ data }: { data: NodeData }) {
  const onChange = useCallback((evt: any, k: StatementKind, updated: number) => {
    data.thisNode.statementList(k).update(updated, evt.target.value);
  }, [data]);

  const afterStatementEdit = useCallback(() => {
    data.thisNode.checkSyntax();
    data.thisNode.setWrappers();
  }, [data]);

  const getStatementFromIndex = (k: StatementKind, index: number) => {
    switch(k) {
      case "given": return data.givens[index];
      case "goal": return data.goals[index];
      default: return data.proofSteps[index];
      // default: return data.proofSteps[index];
    }
  }
  const makeStatementProps = useCallback((k: StatementKind, index: number) => ({
    statement: getStatementFromIndex(k, index),
    index: localIndexToAbsolute(data, k, index),
    onChange: (e: any) => onChange(e, k, index),
    addAbove: () => data.thisNode.statementList(k).add(index),
    addBelow: () => data.thisNode.statementList(k).add(index + 1),
    deleteStatement: () => data.thisNode.statementList(k).remove(index),
    afterEdit: () => afterStatementEdit(),
  }), [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();
  const { isOpen: isSolveNotReadyOpen, onOpen: onSolveNotReadyOpen, onClose: onSolveNotReadyClose } = useDisclosure();
  const { isOpen: isSolveModalOpen, onOpen: onSolveModalOpen, onClose: onSolveModalClose } = useDisclosure();

  const componentStyle = data.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const checkSyntaxButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.thisNode.checkSyntax() }}>Check Syntax</Button>;
  const checkSatButton: ReactNode = 
    <Button size='xs' 
      colorScheme='blackAlpha' 
      onClick={() => { 
        onSolveModalOpen();
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
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.thisNode.delete() }}>Yes, I'm sure!</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>
    
  const checkSolveReady = data.givens.concat(data.proofSteps, data.goals, data.declarationsRef.current).every((s) => s.parsed !== undefined);
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
          <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center'}}>
            <Heading size='sm' >Given</Heading>
            <IconButton
                variant='outline'
                aria-label='Add given'
                size='xs'
                onClick={() => { data.thisNode.givens.add() }}
                icon={<AddIcon />}
              />
          </div>
          {data.givens.map((s: StatementType, index: number) =>
            <Statement 
              {...makeStatementProps("given", index)}
            />)}
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
        <div style={{display: 'flex', justifyContent: 'center'}}>
        {data.correctImplication === undefined &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check incoming implications
        </Button>}
        {data.correctImplication === true &&
          <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
            Check passed. Check again?
          </Button>}
        {data.correctImplication === false &&
          <Button colorScheme='red' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
            Check failed. Check again?
          </Button>}
        </div>
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between'}}>
            <Heading size='sm' >Goal</Heading>
            <IconButton
                variant='outline'
                aria-label='Add given'
                size='xs'
                onClick={() => { data.thisNode.givens.add() }}
                icon={<AddIcon />}
                style={{justifySelf: 'flex-end'}}
              />
          </div>
          {data.givens.map((s: StatementType, index: number) =>
            <Statement 
              {...makeStatementProps("given", index)}
            />)}
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
      <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
        Check incoming implications
      </Button>}
      {data.correctImplication === true &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check passed. Check again?
        </Button>}
      {data.correctImplication === false &&
        <Button colorScheme='red' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check failed. Check again?
        </Button>}
      </div>
      
      {/* Begin: Givens */}
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
        <Text>Givens</Text>
        <IconButton
          variant='outline'
          aria-label='Add given'
          size='xs'
          onClick={() => { data.thisNode.givens.add() }}
          icon={<AddIcon />}
        />
      </div>

      {/* Begin: Given Statements */}
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {data.givens.map((s: StatementType, index: number) =>
          <Statement
            proofNode={true}
            {...makeStatementProps("given", index)}
          />)}
      </div>
      {/* END: Given Statements */}
      {/* END: Givens */}


      {/* BEGIN: Proof */}
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
        <Text>Proof Steps</Text>
        <IconButton
          variant='outline'
          aria-label='Add proof step'
          size='xs'
          onClick={() => { data.thisNode.proofSteps.add() }}
          icon={<AddIcon />}
        />
      </div>

      {/* BEGIN: Proof Statements collapsed*/}
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {componentStyle === "given-node" && givenTitle}
        {componentStyle === "goal-node" && goalTitle}
        {
          isCollapsed ?
            <>
              <Statement
                proofNode={true}
                {...makeStatementProps("proofStep", 0)}
              />
              <Text as='b'>. . .</Text>
              <Statement
                proofNode={true}
                {...makeStatementProps("proofStep", data.proofSteps.length - 1)}
              />
            </> :
            data.proofSteps.map((s: StatementType, index: number) =>
              <Statement
                proofNode={true}
                {...makeStatementProps("proofStep", index)}
              />)
        }
        {/* END: Proof Statements collapsed*/}
        {/* END: Proof */}

        {/* BEGIN: Goals */}
        <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
          <Text>Goals</Text>
          <IconButton
            variant='outline'
            aria-label='Add goal'
            size='xs'
            onClick={() => { data.thisNode.goals.add() }}
            icon={<AddIcon />}
          />
        </div>

        {/* BEGIN: Proof Statements */}
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          {data.goals.map((s: StatementType, index: number) =>
            <Statement
              proofNode={true}
              {...makeStatementProps("goal", index)}
            />)}
        </div>
        {/* END: Proof Statements */}
        {/* END: Goals */}

        {/* BEGIN: Node End Buttons */}
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {data.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
          {checkSyntaxButton}
          {checkSolveReady ? checkSatButton : solveNotReadyPopover}
        </div>
        {/* END: Node End Buttons */}

      </div>
      {componentStyle !== "goal-node" && sourceHandle}
    </Box>
  );
}

export default TextUpdaterNode;
