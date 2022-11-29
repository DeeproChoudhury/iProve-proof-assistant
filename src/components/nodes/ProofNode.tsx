import {
  Box, Button, Popover, PopoverArrow, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, useDisclosure} from '@chakra-ui/react';
import { ReactNode, useCallback, useState } from 'react';
import { Handle, NodeProps, Position } from 'reactflow';
import { StatementNodeData } from '../../types/Node';
import { localIndexToAbsolute } from '../../util/nodes';
import SolveNodeModal from '../SolveNodeModal';
import StatementList from '../StatementList';
import { DeleteNodePopover } from './GeneralNode';

function ProofNode({ data }: NodeProps<StatementNodeData>) {
  const afterStatementEdit = useCallback(() => {
    data.thisNode.checkSyntax();
    data.thisNode.setWrappers();
  }, [data]);

  const [isCollapsed, setCollapsed] = useState(false);
  const { isOpen: isSolveNotReadyOpen, onOpen: onSolveNotReadyOpen, onClose: onSolveNotReadyClose } = useDisclosure();
  const { isOpen: isSolveModalOpen, onOpen: onSolveModalOpen, onClose: onSolveModalClose } = useDisclosure();

  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const checkSatButton: ReactNode = 
    <Button size='xs' 
      colorScheme='blackAlpha' 
      onClick={() => { 
        data.thisNode.checkSyntax();
        onSolveModalOpen();
      }}>
      Solve
    </Button>;
  
  const checkSolveReady = data.parsed === true;
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
    <Box className="proof-node">
      {targetHandle}
      {isSolveModalOpen && <SolveNodeModal 
        isOpen={isSolveModalOpen} 
        onClose={onSolveModalClose} 
        node={data}/>}
      <div style={{display: 'flex', justifyContent: 'center'}}>
      {data.correctImplication === undefined &&
      <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
        Check incoming implications
      </Button>}
      {data.correctImplication === "valid" &&
        <Button colorScheme='whatsapp' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check passed. Check again?
        </Button>}
      {data.correctImplication === "invalid" &&
        <Button colorScheme='red' size='xs' onClick={() => {data.thisNode.checkEdges()}}>
          Check failed. Check again?
        </Button>}
      </div>
      {/* BEGIN: Givens */}
      <StatementList 
        title="Givens"
        statements={data.givens}
        callbacks={data.thisNode.givens}
        indexToDisplayedIndex={index => localIndexToAbsolute(data, "givens", index)}
        afterStatementEdit={afterStatementEdit}
      />
      {/* END: Givens */}


      {/* BEGIN: Proof */}
      <StatementList 
        title="Proof Steps"
        statements={data.proofSteps}
        callbacks={data.thisNode.proofSteps}
        isCollapsed={isCollapsed}
        indexToDisplayedIndex={index => localIndexToAbsolute(data, "proofSteps", index)}
        afterStatementEdit={afterStatementEdit}
      />
      {/* END: Proof */}

      {/* BEGIN: Goals */}
      <StatementList 
        title="Goals"
        statements={data.goals}
        callbacks={data.thisNode.goals}
        indexToDisplayedIndex={index => localIndexToAbsolute(data, "goals", index)}
        afterStatementEdit={afterStatementEdit}
      />
      {/* END: Goals */}

      {/* BEGIN: Node End Buttons */}
      <div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
        <DeleteNodePopover deleteNode={data.thisNode.delete} />
        {data.proofSteps.length >= 3 && !isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => setCollapsed(true)}>Hide</Button>}
        {isCollapsed && <Button size='xs' colorScheme='blackAlpha' onClick={() => { setCollapsed(false) }}>Show</Button>}
        {/* {checkSyntaxButton} */}
        {checkSolveReady ? checkSatButton : solveNotReadyPopover}
      </div>
      {/* END: Node End Buttons */}
      {sourceHandle}
    </Box>
  );
}

export default ProofNode;
