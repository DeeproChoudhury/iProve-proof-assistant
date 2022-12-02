import { Popover, PopoverTrigger, Button, PopoverContent, PopoverArrow, PopoverCloseButton, PopoverHeader, PopoverBody, useDisclosure } from "@chakra-ui/react";
import { AnyNodeData } from "../../types/Node";

export function DeleteNodePopover({ deleteNode }: { deleteNode: () => void }) {
  const { isOpen, onOpen, onClose } = useDisclosure();
	return <Popover isOpen={isOpen} onClose={onClose}>
		<PopoverTrigger>
			<Button size='xs' colorScheme='blackAlpha' onClick={onOpen}>Delete</Button>
		</PopoverTrigger>
		<PopoverContent style={{zIndex:"5"}}>
			<PopoverArrow />
			<PopoverCloseButton />
			<PopoverHeader>Are you sure you want to delete?</PopoverHeader>
			<PopoverBody style={{ display: 'flex', justifyContent: 'space-between' }}>
				<Button size='xs' colorScheme='blackAlpha' onClick={deleteNode}>Yes, I'm sure!</Button>
				<Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
			</PopoverBody>
		</PopoverContent>
	</Popover>;
}

/**
 * Popover for deleting Node 
 * 
 * @param isOpen open popover if true
 * @param onClose function to close popover
 * @param onOpen function to open popover
 * @param nodeData node (InductionData | NodeData) to be deleted 
 * @returns 
 */
export function deleteNodePopover(isOpen: boolean, onClose: () => void, onOpen: () => void, nodeData: AnyNodeData) {
	return <Popover isOpen={isOpen} onClose={onClose}>
		<PopoverTrigger>
			<Button size='xs' colorScheme='blackAlpha' onClick={onOpen}>Delete</Button>
		</PopoverTrigger>
		<PopoverContent>
			<PopoverArrow />
			<PopoverCloseButton />
			<PopoverHeader>Are you sure you want to delete?</PopoverHeader>
			<PopoverBody style={{ display: 'flex', justifyContent: 'space-between' }}>
				<Button size='xs' colorScheme='blackAlpha' onClick={() => { nodeData.thisNode.delete(); } }>Yes, I'm sure!</Button>
				<Button size='xs' colorScheme='blackAlpha' onClick={onClose}>No, go back.</Button>
			</PopoverBody>
		</PopoverContent>
	</Popover>;
};
