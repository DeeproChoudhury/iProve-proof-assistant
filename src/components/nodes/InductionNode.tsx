import { InductionNodeData, ListField } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, Divider, IconButton, Select, Text
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

	const onTypeSelect = (typeIndex: number, index: number) => {
		if (!isNaN(typeIndex)) {
			nodeData.thisNode["types"].updateWithStatement(index, nodeData.typeDeclarationsRef.current[typeIndex]);
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
						<Button variant="outline" colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check incoming implications
						</Button>}
					{nodeData.edgesStatus === "valid" &&
						<Button variant="outline" colorScheme='whatsapp' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check passed. Check again?
						</Button>}
					{nodeData.edgesStatus === "invalid" &&
						<Button variant="outline" colorScheme='red' size='xs' onClick={() => { nodeData.thisNode.checkEdges() }}>
							Check failed. Check again?
						</Button>}
				</div>

				{/* BEGIN : Type */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
					<Text>Type(s)</Text>
					<IconButton
						variant='outline'
						aria-label='Add Induction Goal'
						size='xs'
						icon={<AddIcon />}
						onClick={() => { nodeData.thisNode.types.add() }}
					/>
				</div>
				<div style={{ display: 'flex', flexDirection: 'column', marginTop: "10px" }}>
					{nodeData.types.map((s: StatementType, index: number) =>
						<Select
							placeholder='Select type'
							size='sm'
							style={{backgroundColor: "rgb(252, 248, 242)", borderRadius: "3px"}}
							onChange={e => onTypeSelect(parseInt(e.target.value), index)}
							key={index}>
								{nodeData.typeDeclarationsRef.current.map((type, idx_) =>
									<option value={idx_}>{type.value}</option>
								)}
							
							</Select>)}
				</div>
				{/* END : Type */}

				<Divider style={{padding: "7px 0 7px 0", color: "gray"}}/>

				{/* BEGIN : Motive */}
				<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
					<Text>Induction Goal(s)</Text>
					<IconButton
						variant='outline'
						aria-label='Add Induction Goal'
						size='xs'
						icon={<AddIcon />}
						onClick={() => { nodeData.thisNode.motive.add() }}
					/>
				</div>
				<div style={{ display: 'flex', flexDirection: 'column' }}>
					{nodeData.motive.map((s: StatementType, index: number) =>
						<Statement
							onChange={e => onChange(e, "motive", index)}
							statement={s}
							index={index}
							addAbove={() => {nodeData.thisNode.motive.add(index) }}
							addBelow={() => {nodeData.thisNode.motive.add(index + 1) }}
							deleteStatement={() => { nodeData.thisNode.motive.remove(index) }}
							afterEdit={() => afterStatementEdit("motive", index)}
							key={index} />)}
				</div>
				{/* END : Motive */}

				<Divider style={{padding: "7px 0 7px 0", color: "gray"}}/>

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
							addAbove={() => { nodeData.thisNode.baseCases.add(index) }}
							addBelow={() => { nodeData.thisNode.baseCases.add(index + 1) }}
							deleteStatement={() => { nodeData.thisNode.baseCases.remove(index) }}
							afterEdit={() => afterStatementEdit("baseCases", index)}
							key={index} />)}
				</div>
				{/* END : Base Case */}

				<Divider style={{padding: "7px 0 7px 0", color: "gray"}}/>

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
