import { InductionNodeData, ListField } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, IconButton, Select, Text
} from '@chakra-ui/react';
import { ReactElement, ReactNode, useCallback, useEffect, useState } from "react";
import "./InductionNode.css"
import { Handle, NodeProps, Position } from "reactflow";
import Statement from "../Statement";
import { StatementType } from "../../types/Statement";
import { DeleteNodePopover } from "./GeneralNode";
import Moveable from "react-moveable";
import { MoveableHandles } from "./MoveableHandle";
import { makeRecheckCallback } from "../../util/nodes";

function InductionNode({ id, data: nodeData }: NodeProps<InductionNodeData>): ReactElement {
	const [target, setTarget] = useState<any>();
	
	useEffect(() => {
		return setTarget(document.querySelector(`#induction-node-${id}`)!);
	}, [id]);
	const statusStyle = nodeData.internalsStatus !== 'unchecked' ? nodeData.internalsStatus + "-induction" : '';
	const componentStyle = "induction-node " + statusStyle;
	const onChange = useCallback((evt: any, k: ListField<InductionNodeData>, updated: number) => {
		nodeData.thisNode[k].update(updated, evt.target.value);
	}, [nodeData]);

  const afterStatementEdit = useCallback(makeRecheckCallback({ type: "inductionNode", data: nodeData }), [nodeData]);

  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const checkSatButton: ReactNode = 
    <Button size='xs'
      colorScheme='blackAlpha' 
      onClick={() => { 
		nodeData.thisNode.checkInternal();
      }}>
      Check induction principle
    </Button>;
	
	const NodeBottomButtons = () => {
		return (
			<div style={{ display: 'flex', justifyContent: 'space-between', marginTop: '5px' }}>
				<DeleteNodePopover deleteNode={nodeData.thisNode.delete} />
				{checkSatButton}
			</div>
		);
	}

	const onTypeSelect = (typeIndex: number) => {
		if (!isNaN(typeIndex)) {
			nodeData.thisNode["types"].updateWithStatement(0, nodeData.typeDeclarationsRef.current[typeIndex]);
		}
	}

	/**
	 * INDUCTION NODE
	 */
	return (
		<div>
			<Box className={componentStyle} key={`induction-node-${id}`} id={`induction-node-${id}`}>
				{targetHandle}
				<div style={{ display: 'flex', justifyContent: 'center' }}>
					{nodeData.edgesStatus === "unchecked" &&
						<Button colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check incoming implications
						</Button>}
					{nodeData.edgesStatus === "valid" &&
						<Button colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check passed. Check again?
						</Button>}
					{nodeData.edgesStatus === "invalid" &&
						<Button colorScheme='red' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check failed. Check again?
						</Button>}
				</div>

				{/* BEGIN : Type */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between' }}>
					<Text>Type</Text>
				</div>
				<Select placeholder='Select type' size='xs' onChange={(event) => onTypeSelect(parseInt(event.target.value))} defaultValue={nodeData.types[0].value}>
					{nodeData.typeDeclarationsRef.current.map((type, index) =>
						<option value={index}>{type.value}</option>
					)}
				</Select>
				{/* END : Type */}

				{/* BEGIN : Motive */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
					<Text>Induction Goal</Text>
				</div>
				<Statement
					onChange={e => onChange(e, "motive", 0)}
					statement={nodeData.motive[0]}
					index={0}
					addAbove={() => { }}
					addBelow={() => { }}
					deleteStatement={() => { }}
					afterEdit={() => afterStatementEdit("motive", 0)}
					proofNode={false} />
				{/* <Handle type="source" position={Position.Left} id="l" style={{ height: '10px', width: '10px' }} /> */}
				{/* END : Motive */}

				{/* BEGIN : Base Case */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
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
							deleteStatement={() => { nodeData.thisNode.baseCases.remove(index) }}
							afterEdit={() => afterStatementEdit("baseCases", index)}
							key={index} />)}
				</div>
				{/* END : Base Case */}

				{/* BEGIN : Induction Case */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
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
							deleteStatement={() => { nodeData.thisNode.inductiveCases.remove(index) }}
							afterEdit={() => afterStatementEdit("inductiveCases", index)}
							key={index} />)}
				</div>
				{/* END : Induction Case */}

				{/* START : Node Bottom Buttons */}
				<NodeBottomButtons />
				{/* END : Node Bottom Buttons */}

				{sourceHandle}
			</Box>

			{/* BEGIN: Moveable component to allow horizontal resizing */}
			<MoveableHandles target={target}/>
			{/* END: Moveable component to allow horizontal resizing */}
		
		</div>
	)

}

export default InductionNode;
