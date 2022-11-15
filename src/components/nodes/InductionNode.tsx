import { InductionData } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, Heading, IconButton, Popover, PopoverArrow, PopoverBody, PopoverCloseButton, PopoverContent,
	PopoverHeader, PopoverTrigger, Text, useDisclosure
} from '@chakra-ui/react';
import { ReactElement, ReactNode } from "react";
import "./InductionNode.css"
import { Handle, Position } from "reactflow";

function InductionNode({ data }: { data: InductionData }) : ReactElement {
	const componentStyle = data.type + "-node";
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
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { data.thisNode.delete() }}>Yes, I'm sure!</Button>
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
		<Box className={componentStyle}>

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
				/>
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