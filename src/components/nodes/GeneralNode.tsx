import { Popover, PopoverTrigger, Button, PopoverContent, PopoverArrow, PopoverCloseButton, PopoverHeader, PopoverBody } from "@chakra-ui/react";
import { ReactElement } from "react";
import { GeneralNodeData, InductionData, NodeData } from "../../types/Node";
import InductionNode from "./InductionNode";
import TextUpdaterNode from "./TextUpdaterNode";

/*  */
export default function GeneralNode( { data } : { data : GeneralNodeData } ) : ReactElement {
    if (data.type === "induction") {
        // data = data as InductionData;
        const nodeData : InductionData = data as InductionData;
        return InductionNode({ data : nodeData });
    } else {
        const nodeData : NodeData = data as NodeData;
        return TextUpdaterNode({ data : nodeData });
    }
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
export function deleteNodePopover(isOpen: boolean, onClose: () => void, onOpen: () => void, nodeData: InductionData | NodeData) {
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