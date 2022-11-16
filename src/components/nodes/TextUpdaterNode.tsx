import { AddIcon } from '@chakra-ui/icons';
import {
  Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactElement, ReactNode, useCallback, useState } from 'react';
import { Handle, Position } from 'reactflow';
import { ASTSMTLIB2 } from '../../parser/AST';
import { GeneralNodeData, NodeData } from '../../types/Node';
import { StatementKind, StatementType } from '../../types/Statement';
import SolveNodeModal from '../SolveNodeModal';
import Statement from '../Statement';
import { deleteNodePopover } from './GeneralNode';

function TextUpdaterNode({ data: nodeData }: { data: NodeData }) : ReactElement {
  const onChange = useCallback((evt: any, k: StatementKind, updated: number) => {
    nodeData.thisNode.statementList(k).update(updated, evt.target.value);
  }, [nodeData]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen, onOpen, onClose } = useDisclosure();
  const { isOpen: isSolveNotReadyOpen, onOpen: onSolveNotReadyOpen, onClose: onSolveNotReadyClose } = useDisclosure();
  const { isOpen: isSolveModalOpen, onOpen: onSolveModalOpen, onClose: onSolveModalClose } = useDisclosure();

  const componentStyle = nodeData.type + "-node";
  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const checkSyntaxButton: ReactNode = <Button size='xs' colorScheme='blackAlpha' onClick={() => { nodeData.thisNode.checkSyntax() }}>Check Syntax</Button>;
  const checkSatButton: ReactNode = 
    <Button size='xs' 
      colorScheme='blackAlpha' 
      onClick={() => { 
        onSolveModalOpen();
        console.log(nodeData.proofSteps);
        console.log(nodeData.proofSteps.map(x => {
          return (x.parsed?.kind !== "FunctionDeclaration") ? `(assert ${ASTSMTLIB2(x.parsed)})` : ASTSMTLIB2(x.parsed);
        }).join("\n"));
      }}>
      Solve
    </Button>;
  
  // Delete Node button popover
  const deletePopover =
    deleteNodePopover(isOpen, onClose, onOpen, nodeData)
    
    
  const checkSolveReady = nodeData.givens.concat(nodeData.proofSteps, nodeData.goals, nodeData.declarationsRef.current).every((s) => s.parsed !== undefined);
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

  const NodeBottomButtons = () => {
    return (
    <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
      {deletePopover}
      {checkSyntaxButton}
      {checkSatButton}
    </div>
    );
  }

  
  /**
   * GIVEN NODE :
   */
  if (nodeData.type === "given") {
    return GivenNode(componentStyle, nodeData, onChange, NodeBottomButtons, sourceHandle);
  };


  /**
   * GOAL NODE : 
   */
  if (nodeData.type === "goal") {
    return GoalNode(componentStyle, targetHandle, nodeData, onChange, NodeBottomButtons)
  }
  

  return (
    <Box className={componentStyle}>
      {componentStyle !== "given-node" && targetHandle}
      <SolveNodeModal 
        isOpen={isSolveModalOpen} 
        onClose={onSolveModalClose} 
        node={nodeData}/>
      <div style={{display: 'flex', justifyContent: 'center'}}>
      {nodeData.correctImplication === undefined &&
      <Button colorScheme='whatsapp' size='xs' onClick={() => {nodeData.thisNode.checkEdges()}}>
        Check incoming implications
      </Button>}
      {nodeData.correctImplication === true &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {nodeData.thisNode.checkEdges()}}>
          Check passed. Check again?
        </Button>}
      {nodeData.correctImplication === false &&
        <Button colorScheme='red' size='xs' onClick={() => {nodeData.thisNode.checkEdges()}}>
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
          onClick={() => { nodeData.thisNode.givens.add() }}
          icon={<AddIcon />}
        />
      </div>

      {/* Begin: Given Statements */}
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {nodeData.givens.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, "given", index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { nodeData.thisNode.givens.add(index) }}
            addBelow={() => { nodeData.thisNode.givens.add(index + 1) }} 
            deleteStatement = {() => {nodeData.thisNode.givens.remove(index)}}
            setWrappers={() => {nodeData.thisNode.setWrappers()}}/>)}
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
          onClick={() => { nodeData.thisNode.proofSteps.add() }}
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
                statement={nodeData.proofSteps[0]}
                index={nodeData.givens.length}
                proofNode={true}
                addAbove={() => { nodeData.thisNode.proofSteps.add(0) }}
                addBelow={() => { nodeData.thisNode.proofSteps.add(1) }}
                deleteStatement={() => { nodeData.thisNode.proofSteps.remove(0) }} 
                setWrappers={() => {nodeData.thisNode.setWrappers()}}/>
              <Text as='b'>. . .</Text>
              <Statement
                onChange={e => onChange(e, "proofStep", nodeData.proofSteps.length - 1)}
                statement={nodeData.proofSteps[nodeData.proofSteps.length - 1]}
                index={nodeData.givens.length + nodeData.proofSteps.length - 1}
                proofNode={true}
                addAbove={() => { nodeData.thisNode.proofSteps.add(nodeData.proofSteps.length - 1) }}
                addBelow={() => { nodeData.thisNode.proofSteps.add(nodeData.proofSteps.length) }} 
                deleteStatement={() => { nodeData.thisNode.proofSteps.remove(nodeData.proofSteps.length - 1) }}
                setWrappers={() => {nodeData.thisNode.setWrappers()}}/>
            </> :
            nodeData.proofSteps.map((s: StatementType, index: number) =>
              <Statement
                onChange={e => onChange(e, "proofStep", index)}
                statement={s}
                index={nodeData.givens.length + index}
                proofNode={true}
                addAbove={() => { nodeData.thisNode.proofSteps.add(index) }}
                addBelow={() => { nodeData.thisNode.proofSteps.add(index + 1) }} 
                deleteStatement={() => { nodeData.thisNode.proofSteps.remove(index) }}
                setWrappers={() => {nodeData.thisNode.setWrappers()}} />)
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
            onClick={() => { nodeData.thisNode.goals.add() }}
            icon={<AddIcon />}
          />
        </div>

        {/* BEGIN: Proof Statements */}
        <div style={{ display: 'flex', flexDirection: 'column' }}>
          {nodeData.goals.map((s: StatementType, index: number) =>
            <Statement
              onChange={e => onChange(e, "goal", index)}
              statement={s}
              index={nodeData.givens.length + nodeData.proofSteps.length + index}
              proofNode={true}
              addAbove={() => { nodeData.thisNode.goals.add(index) }}
              addBelow={() => { nodeData.thisNode.goals.add(index + 1) }} 
              deleteStatement = {() => {nodeData.thisNode.goals.remove(index)}}
              setWrappers={() => {nodeData.thisNode.setWrappers()}}/>)}
        </div>
        {/* END: Proof Statements */}
        {/* END: Goals */}

        {/* BEGIN: Node End Buttons */}
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          {deletePopover}
          {nodeData.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
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
function GoalNode(componentStyle: string, targetHandle: ReactNode, nodeData: NodeData, onChange: (evt: any, k: StatementKind, updated: number) => void, NodeBottomButtons: () => JSX.Element) {
  return <Box className={componentStyle}>
    {targetHandle}
    <div style={{ display: 'flex', justifyContent: 'center' }}>
      {nodeData.correctImplication === undefined &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges(); } }>
          Check incoming implications
        </Button>}
      {nodeData.correctImplication === true &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges(); } }>
          Check passed. Check again?
        </Button>}
      {nodeData.correctImplication === false &&
        <Button colorScheme='red' size='xs' onClick={() => { nodeData.thisNode.checkEdges(); } }>
          Check failed. Check again?
        </Button>}
    </div>
    <div style={{ display: 'flex', flexDirection: 'column' }}>
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
        <Heading size='sm'>Goal</Heading>
        <IconButton
          variant='outline'
          aria-label='Add given'
          size='xs'
          onClick={() => { nodeData.thisNode.givens.add(); } }
          icon={<AddIcon />}
          style={{ justifySelf: 'flex-end' }} />
      </div>
      {nodeData.givens.map((s: StatementType, index: number) => <Statement
        onChange={e => onChange(e, "given", index)}
        statement={s}
        index={index}
        addAbove={() => { nodeData.thisNode.givens.add(index); } }
        addBelow={() => { nodeData.thisNode.givens.add(index + 1); } }
        deleteStatement={() => { nodeData.thisNode.givens.remove(index); } }
        setWrappers={() => { nodeData.thisNode.setWrappers(); } } />)}
    </div>

    {/* START : Node Bottom Buttons */}
    <NodeBottomButtons />
    {/* END : Node Bottom Buttons */}

  </Box>;
}

function GivenNode(componentStyle: string, nodeData: NodeData, onChange: (evt: any, k: StatementKind, updated: number) => void, NodeBottomButtons: () => JSX.Element, sourceHandle: ReactNode) {
  return <Box className={componentStyle}>
    <div style={{ display: 'flex', flexDirection: 'column' }}>
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center' }}>
        <Heading size='sm'>Given</Heading>
        <IconButton
          variant='outline'
          aria-label='Add given'
          size='xs'
          onClick={() => { nodeData.thisNode.givens.add(); } }
          icon={<AddIcon />} />
      </div>
      {nodeData.givens.map((s: StatementType, index: number) => <Statement
        onChange={e => onChange(e, "given", index)}
        statement={s}
        index={index}
        addAbove={() => { nodeData.thisNode.givens.add(index); } }
        addBelow={() => { nodeData.thisNode.givens.add(index + 1); } }
        deleteStatement={() => { nodeData.thisNode.givens.remove(index); } }
        setWrappers={() => { nodeData.thisNode.setWrappers(); } } />)}
    </div>

    {/* START : Node Bottom Buttons */}
    <NodeBottomButtons />
    {/* END : Node Bottom Buttons */}

    {sourceHandle}
  </Box>;
}

