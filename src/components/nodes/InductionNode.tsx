import { InductionData } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
	PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactElement, ReactNode, useCallback } from "react";
import "./InductionNode.css"
import { Handle, Position } from "reactflow";
import Statement from "../Statement";
import { StatementKind, StatementType } from "../../types/Statement";

function InductionNode({ data: nodeData }: { data: InductionData }) : ReactElement {
	const componentStyle = nodeData.type + "-node";
  const onChange = useCallback((evt: any, k: StatementKind, updated: number) => {
    nodeData.thisNode.statementList(k).update(updated, evt.target.value);
  }, [nodeData]);
  const { isOpen, onOpen, onClose } = useDisclosure();

  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const givenTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Given</Heading>
  const goalTitle: ReactNode = <Heading textAlign={['center']} as='h6' size='xs'>Goal</Heading>
  
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
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { nodeData.thisNode.delete() }}>Yes, I'm sure!</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>
	
	const NodeBottomButtons = () => {
		return (
			<div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
				{deletePopover}
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
				<IconButton
					variant='outline'
					aria-label='Add Type'
					size='xs'
					icon={<AddIcon />}
				/>
			</div>
			{/* END : Type */}

			{/* BEGIN : Base Case */}
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
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
            onChange={e => onChange(e, "baseCase", index)}
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
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
				<Text>Inductive Case(s)</Text>
				<IconButton
					variant='outline'
					aria-label='Add given'
					size='xs'
					icon={<AddIcon />}
				/>
			</div>
			{/* END : Induction Case */}

			{/* START : Node Bottom Buttons */}
			<NodeBottomButtons />
			{/* END : Node Bottom Buttons */}

		</Box>

	)

}

export default InductionNode;