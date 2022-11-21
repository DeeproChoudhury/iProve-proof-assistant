import { GeneralNodeData, InductionData, ListField } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
	PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactElement, ReactNode, useCallback } from "react";
import "./InductionNode.css"
import { Handle, Position } from "reactflow";
import Statement from "../Statement";
import { StatementType } from "../../types/Statement";
import { deleteNodePopover } from "./GeneralNode";

function InductionNode({ data: nodeData }: { data: InductionData }) : ReactElement {
	const componentStyle = nodeData.type + "-node";
  const onChange = useCallback((evt: any, k: ListField<InductionData>, updated: number) => {
    nodeData.thisNode[k].update(updated, evt.target.value);
  }, [nodeData]);
  const { isOpen, onOpen, onClose } = useDisclosure();

  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  const checkSatButton: ReactNode = 
    <Button size='xs'
      colorScheme='blackAlpha' 
      onClick={() => { 
        console.log(nodeData.baseCases);
        console.log(nodeData.inductiveCases);
        console.log(nodeData.inductiveHypotheses[0]);
        console.log(nodeData.types[0]);
        console.log(nodeData.predicate[0]);
				console.log('types: ', nodeData.typeDeclarationsRef.current);
      }}>
      Solve
    </Button>;
  // Delete Node button popover
	const deletePopover =
    deleteNodePopover(isOpen, onClose, onOpen, nodeData)
	
	const NodeBottomButtons = () => {
		return (
			<div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
				{deletePopover}
				{checkSatButton}
			</div>
		);
	}

	/**
 * INDUCTION NODE
 */
	return (
		<Box className={componentStyle} key={`induction-node-${nodeData.id}`}>

			{/* BEGIN : Type */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
				<Text>Type</Text>
			</div>
			<Statement
				onChange={e => onChange(e, "types", 0)}
				statement={nodeData.types[0]}
				addAbove={() => {}}
				addBelow={() => {}}
				deleteStatement={() => {}}
				index={0}
				proofNode={false}/>
			{/* END : Type */}

			{/* BEGIN : Predicate */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
				<Text>Predicate</Text>
			</div>
			<Statement
				onChange={e => onChange(e, "predicate", 0)}
				statement={nodeData.predicate[0]}
				index={0}
				addAbove={() => {}}
				addBelow={() => {}}
				deleteStatement={() => {}}
				proofNode={false}/>
			{/* END : Predicate */}

			{/* BEGIN : Base Case */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px'}}>
				<Text>Base Case(s)</Text>
				<IconButton
					variant='outline'
					aria-label='Add Base Case'
					size='xs'
					icon={<AddIcon />}
					onClick={() => { nodeData.thisNode.baseCases.add() }}
				/>
			</div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {nodeData.baseCases.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, "baseCases", index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { nodeData.thisNode.baseCases.add(index) }}
            addBelow={() => { nodeData.thisNode.baseCases.add(index + 1) }} 
            deleteStatement = {() => {nodeData.thisNode.baseCases.remove(index)}}
						key={index}/>)}
      </div>
			{/* END : Base Case */}

			{/* BEGIN : Induction Case */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px'}}>
				<Text>Inductive Case(s)</Text>
				<IconButton
					variant='outline'
					aria-label='Add given'
					size='xs'
					icon={<AddIcon />}
					onClick={() => { nodeData.thisNode.inductiveCases.add() }}
				/>
			</div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {nodeData.inductiveCases.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, "inductiveCases", index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { nodeData.thisNode.inductiveCases.add(index) }}
            addBelow={() => { nodeData.thisNode.inductiveCases.add(index + 1) }} 
            deleteStatement = {() => {nodeData.thisNode.inductiveCases.remove(index)}}
						key={index}/>)}
      </div>
			{/* END : Induction Case */}


			{/* BEGIN : Inductive Hypothesis */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px'}}>
				<Text>Inductive Hypothesis</Text>
			</div>
			<Statement
				onChange={e => onChange(e, "inductiveHypotheses", 0)}
				statement={nodeData.inductiveHypotheses[0]}
				index={0}
				addAbove={() => {}}
				addBelow={() => {}}
				deleteStatement={() => {}}
				proofNode={false}/>
			{/* END : Inductive Hypothesis */}

			{/* START : Node Bottom Buttons */}
			<NodeBottomButtons />
			{/* END : Node Bottom Buttons */}

		</Box>

	)

}

export default InductionNode;
