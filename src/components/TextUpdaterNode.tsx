import { AddIcon } from '@chakra-ui/icons';
import {
  Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { ASTSMTLIB2 } from '../parser/AST';
import { NodeData } from '../types/Node';
import { StatementKind, StatementType } from '../types/Statement';
import SolveNodeModal from './SolveNodeModal';
import Statement from './Statement';

function TextUpdaterNode({ data }: { data: NodeData }) {
  const onChange = useCallback((evt: any, k: StatementKind, updated: number) => {
    data.thisNode.statementList(k).update(updated, evt.target.value);
  }, [data]);

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
        console.log(data.proofSteps);
        console.log(data.proofSteps.map(x => {
          return (x.parsed?.kind !== "FunctionDeclaration") ? `(assert ${ASTSMTLIB2(x.parsed)})` : ASTSMTLIB2(x.parsed);
        }).join("\n"));
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


  /**
   * GIVEN NODE :
   */
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
              onChange={e => onChange(e, "given", index)} 
              statement={s} 
              index={index} 
              addAbove={() => { data.thisNode.givens.add(index) }}
              addBelow={() => { data.thisNode.givens.add(index + 1) }} 
              deleteStatement={() => { data.thisNode.givens.remove(index) }}
              setWrappers={() => {data.thisNode.setWrappers()}} />)}
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


  /**
   * GOAL NODE : 
   */
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
              onChange={e => onChange(e, "given", index)} 
              statement={s} 
              index={index} 
              addAbove={() => { data.thisNode.givens.add(index) }}
              addBelow={() => { data.thisNode.givens.add(index + 1) }} 
              deleteStatement={() => { data.thisNode.givens.remove(index) }}
              setWrappers={() => {data.thisNode.setWrappers()}}/>)}
        </div>
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {checkSyntaxButton}
          {checkSatButton}
        </div>
      </Box>
    )
  }

  /**
   * INDUCTION NODE
   */
  if( data.type === "induction" ) {
    return (
      <Box className={componentStyle}>
        <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
          <Text>Base Case(s)</Text>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            icon={<AddIcon />}
          />
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
            onChange={e => onChange(e, "given", index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { data.thisNode.givens.add(index) }}
            addBelow={() => { data.thisNode.givens.add(index + 1) }} 
            deleteStatement = {() => {data.thisNode.givens.remove(index)}}
            setWrappers={() => {data.thisNode.setWrappers()}}/>)}
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

      {/* BEGIN: Proof Statements */}
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
                addAbove={() => { data.thisNode.proofSteps.add(0) }}
                addBelow={() => { data.thisNode.proofSteps.add(1) }}
                deleteStatement={() => { data.thisNode.proofSteps.remove(0) }} 
                setWrappers={() => {data.thisNode.setWrappers()}}/>
              <Text as='b'>. . .</Text>
              <Statement
                onChange={e => onChange(e, "proofStep", data.proofSteps.length - 1)}
                statement={data.proofSteps[data.proofSteps.length - 1]}
                index={data.givens.length + data.proofSteps.length - 1}
                proofNode={true}
                addAbove={() => { data.thisNode.proofSteps.add(data.proofSteps.length - 1) }}
                addBelow={() => { data.thisNode.proofSteps.add(data.proofSteps.length) }} 
                deleteStatement={() => { data.thisNode.proofSteps.remove(data.proofSteps.length - 1) }}
                setWrappers={() => {data.thisNode.setWrappers()}}/>
            </> :
            data.proofSteps.map((s: StatementType, index: number) =>
              <Statement
                onChange={e => onChange(e, "proofStep", index)}
                statement={s}
                index={data.givens.length + index}
                proofNode={true}
                addAbove={() => { data.thisNode.proofSteps.add(index) }}
                addBelow={() => { data.thisNode.proofSteps.add(index + 1) }} 
                deleteStatement={() => { data.thisNode.proofSteps.remove(index) }}
                setWrappers={() => {data.thisNode.setWrappers()}} />)
        }
        {/* END: Proof Statements*/}
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
              onChange={e => onChange(e, "goal", index)}
              statement={s}
              index={data.givens.length + data.proofSteps.length + index}
              proofNode={true}
              addAbove={() => { data.thisNode.goals.add(index) }}
              addBelow={() => { data.thisNode.goals.add(index + 1) }} 
              deleteStatement = {() => {data.thisNode.goals.remove(index)}}
              setWrappers={() => {data.thisNode.setWrappers()}}/>)}
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
