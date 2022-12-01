import {
  Box, Button, Popover, PopoverArrow, PopoverCloseButton, PopoverContent,
  PopoverHeader, PopoverTrigger, useDisclosure
} from '@chakra-ui/react';
import { ReactNode, useCallback, useEffect, useState } from 'react';
import Moveable from 'react-moveable';
import { NodeProps } from 'reactflow';
import { StatementNodeData } from '../../types/Node';
import { localIndexToAbsolute } from '../../util/nodes';
import SolveNodeModal from '../SolveNodeModal';
import StatementList from '../StatementList';
import { DeleteNodePopover } from './GeneralNode';
import { NodeHandle } from './NodeHandle';

function ProofNode({ id, data }: NodeProps<StatementNodeData>) {
  const afterStatementEdit = useCallback(() => {
    data.thisNode.checkSyntax();
    data.thisNode.setWrappers();
  }, [data]);
  const [target, setTarget] = useState<any>();
  const [frame] = useState<any>({
    translate: [0, 0],
  });
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
          {data.correctImplication === undefined &&
            <Button colorScheme='whatsapp' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check incoming implications
            </Button>}
          {data.correctImplication === "valid" &&
            <Button colorScheme='whatsapp' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
              Check passed. Check again?
            </Button>}
          {data.correctImplication === "invalid" &&
            <Button colorScheme='red' size='xs' onClick={() => { data.thisNode.checkEdges() }}>
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

        <NodeHandle type='source' />
      </Box>
      {/* BEGIN: Moveable component to allow horizontal resizing */}
      <Moveable
        target={target}
        resizable={true}
        keepRatio={false}
        throttleResize={1}
        renderDirections={["e", "w"]}
        edge={false}
        zoom={1}
        origin={false}
        padding={{ "left": 0, "top": 0, "right": 0, "bottom": 0 }}
        onResizeStart={e => {
          e.setOrigin(["%", "%"]);
          e.dragStart && e.dragStart.set(frame.translate);
        }}
        onResize={e => {
          const beforeTranslate = e.drag.beforeTranslate;
          frame.translate = beforeTranslate;
          e.target.style.width = `${e.width}px`;
          e.target.style.transform = `translate(${beforeTranslate[0]}px, 0px)`;
        }}
      />
      {/* END: Moveable component to allow horizontal resizing */}
    </div>
  );
}

export default ProofNode;
