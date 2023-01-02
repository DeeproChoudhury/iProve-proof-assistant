import { Popover, PopoverTrigger, Button, PopoverContent, PopoverArrow, PopoverCloseButton, PopoverHeader, PopoverBody, useDisclosure } from "@chakra-ui/react";

export function DeleteNodePopover({ deleteNode }: { deleteNode: () => void }) {
  const { isOpen, onOpen, onClose } = useDisclosure();
	return <Popover isOpen={isOpen} onClose={onClose}>
		<PopoverTrigger>
			<Button size='xs' colorScheme='blackAlpha' onClick={onOpen}>Delete</Button>
		</PopoverTrigger>
		<PopoverContent>
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
