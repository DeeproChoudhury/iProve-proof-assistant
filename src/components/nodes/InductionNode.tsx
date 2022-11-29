import { InductionNodeData, ListField } from "../../types/Node";
import { AddIcon } from '@chakra-ui/icons';
import {
	Box, Button, IconButton, Select, Text
} from '@chakra-ui/react';
import { ReactElement, ReactNode, useCallback } from "react";
import "./InductionNode.css"
import { Handle, NodeProps, Position } from "reactflow";
import Statement from "../Statement";
import { StatementType } from "../../types/Statement";
import { DeleteNodePopover } from "./GeneralNode";

function InductionNode({ id, data: nodeData }: NodeProps<InductionNodeData>) : ReactElement {
	const componentStyle = "induction-node";
  const onChange = useCallback((evt: any, k: ListField<InductionNodeData>, updated: number) => {
    nodeData.thisNode[k].update(updated, evt.target.value);
  }, [nodeData]);

  const afterStatementEdit = useCallback(() => {
    nodeData.thisNode.checkSyntax();
  }, [nodeData]);

  const targetHandle: ReactNode = <Handle type="target" position={Position.Top} style={{ height: '10px', width: '10px' }} />;
  const sourceHandle: ReactNode = <Handle type="source" position={Position.Bottom} id="b" style={{ height: '10px', width: '10px' }} />;
  const checkSatButton: ReactNode = 
    <Button size='xs'
      colorScheme='blackAlpha' 
      onClick={() => { 
		nodeData.thisNode.checkPrinciple();
      }}>
      Solve
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
		<Box className={componentStyle} key={`induction-node-${id}`}>
      {targetHandle}
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
			<div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px'}}>
				<Text>Induction Goal</Text>
			</div>
			<Statement
				onChange={e => onChange(e, "motive", 0)}
				statement={nodeData.motive[0]}
				index={0}
				addAbove={() => {}}
				addBelow={() => {}}
				deleteStatement={() => {}}
				afterEdit={() => afterStatementEdit()}
				proofNode={false}/>
			<Handle type="source" position={Position.Left} id="l" style={{ height: '10px', width: '10px' }} />
			{/* END : Motive */}

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

			{/* START : Node Bottom Buttons */}
			<NodeBottomButtons />
			{/* END : Node Bottom Buttons */}
      {sourceHandle}
		</Box>

	)

}

export default InductionNode;
