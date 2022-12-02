import {
  Box, Button, Divider, Popover, PopoverArrow, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, useDisclosure
} from '@chakra-ui/react';
import { ReactNode, useCallback, useEffect, useState } from 'react';
import { NodeProps } from 'reactflow';
import { ListField, StatementNodeData } from '../../types/Node';
import { allParsed, localIndexToAbsolute, makeRecheckCallback } from '../../util/nodes';
import SolveNodeModal from '../SolveNodeModal';
import StatementList from '../StatementList';
import { DeleteNodePopover } from './GeneralNode';
import { MoveableHandles } from './MoveableHandle';
import { NodeHandle } from './NodeHandle';

function ProofNode({ id, data }: NodeProps<StatementNodeData>) {
  const afterStatementEdit = useCallback(makeRecheckCallback({ type: "proofNode", data }), [data]);
  const [target, setTarget] = useState<any>();
  
  useEffect(() => {
    return setTarget(document.querySelector(`#proof-node-${id}`)!);
  }, [id]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen: isSolveNotReadyOpen, onOpen: onSolveNotReadyOpen, onClose: onSolveNotReadyClose } = useDisclosure();
  const { isOpen: isSolveModalOpen, onOpen: onSolveModalOpen, onClose: onSolveModalClose } = useDisclosure();

  const checkSatButton: ReactNode = 
    <Button size='xs' 
      colorScheme='blackAlpha' 
      onClick={() => { 
        data.thisNode.parseAll();
        onSolveModalOpen();
      }}>
      Solve
    </Button>;
  
  const checkSolveReady = allParsed({type: "proofNode", data});
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

  return (
    <div>
      <Box className="proof-node" id={`proof-node-${id}`}>
        {/* BEGIN : Top Handle */}
        <NodeHandle type='target' />
        {/* END : Top Handle */}

        {isSolveModalOpen && <SolveNodeModal
          isOpen={isSolveModalOpen}
          onClose={onSolveModalClose}
          node={data} />}
        <div style={{ display: 'flex', justifyContent: 'center' }}>
          {data.edgesStatus === "unchecked" &&
            <Button colorScheme='whatsapp' variant="outline" size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check incoming implications
            </Button>}
          {data.edgesStatus === "valid" &&
            <Button colorScheme='whatsapp' variant="outline" size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check passed. Check again?
            </Button>}
          {data.edgesStatus === "invalid" &&
            <Button colorScheme='red' variant="outline" size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check failed. Check again?
            </Button>}
        </div>
        {/* BEGIN: Givens */}
        <StatementList
          title="Givens"
          statements={data.givens}
          callbacks={data.thisNode.givens}
          indexToDisplayedIndex={index => localIndexToAbsolute(data, "givens", index)}
          afterStatementEdit={(index) => afterStatementEdit("givens", index)}
        />
        {/* END: Givens */}
        <Divider style={{padding: "7px 0 7px 0"}}/>


        {/* BEGIN: Proof */}
        <StatementList
          title="Proof Steps"
          statements={data.proofSteps}
          callbacks={data.thisNode.proofSteps}
          isCollapsed={isCollapsed}
          indexToDisplayedIndex={index => localIndexToAbsolute(data, "proofSteps", index)}
          afterStatementEdit={(index) => afterStatementEdit("proofSteps", index)}
        />
        {/* END: Proof */}
        <Divider style={{padding: "7px 0 7px 0"}}/>

        {/* BEGIN: Goals */}
        <StatementList
          title="Goals"
          statements={data.goals}
          callbacks={data.thisNode.goals}
          indexToDisplayedIndex={index => localIndexToAbsolute(data, "goals", index)}
          afterStatementEdit={(index) => afterStatementEdit("goals", index)}
        />
        {/* END: Goals */}

        {/* BEGIN: Node End Buttons */}
        <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
          <DeleteNodePopover deleteNode={data.thisNode.delete} />
          {data.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='gray' onClick={() => setCollapsed(true)}>Hide</Button>}
          {isCollapsed && <Button size='xs' colorScheme='gray' onClick={() => { setCollapsed(false) }}>Show</Button>}
          {/* {checkSyntaxButton} */}
          {checkSolveReady ? checkSatButton : solveNotReadyPopover}
        </div>
        {/* END: Node End Buttons */}

        <NodeHandle type='source' />
      </Box>

      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <MoveableHandles target={target} />
      {/* END: Moveable component to allow horizontal resizing */}
    </div>
  );
}

export default ProofNode;
