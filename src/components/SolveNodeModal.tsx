import {
  Button, Modal, ModalBody,
  ModalCloseButton, ModalContent, ModalFooter, ModalHeader, ModalOverlay, Text, Tooltip
} from '@chakra-ui/react';
import { useState } from 'react';
import { StatementNodeData } from '../types/Node';
import { StatementType } from '../types/Statement';
import { renderError } from '../util/errors';
import { absoluteIndexToLocal } from '../util/nodes';
import { z3Reason } from '../util/reasons';
import { IProveError } from "../types/ErrorLocation";
import ModalStatement from './ModalStatement';
import './SolveNodeModal.css';
import { useStatementNodeActions } from '../store/hooks';

export type SolveNodeModalPropsType = {
  isOpen: boolean,
  onClose: () => void,
  node: StatementNodeData,
  nodeId: string,
}

type Tag = '0' | '1' | '2'; 

const SolveNodeModal = (props: SolveNodeModalPropsType) => {
  const { isOpen, onClose, node, nodeId } = props;
  const nodeActions = useStatementNodeActions(nodeId)
  const [tags, setTags] = useState<Tag[]>(Array(node.givens.length + node.proofSteps.length + node.goals.length).fill('0'));
  const relevantTags = tags.slice(0, node.givens.length + node.proofSteps.length + node.goals.length);
  const [checkError, setCheckFailed] = useState<IProveError | undefined>(undefined);

  const onChange = (v: string, index: number) => {
    setTags(tags => tags.map((t, i) => {
      if (t === '2' && v === '2') {
        return '0';
      }
      if (i === index) {
        return v as Tag;
      }
      if (i > index && v === '2') {
        return '0';
      }
      return t;
    }));
  }

  const isReasonDisabled = (index: number) => {
    return tags.slice(0, index).findIndex((tag) => tag === '2') !== -1;
  }

  const solveZ3 = () => {
    const reasonsIndexes = relevantTags.map((t, i) => t === '1' ? i : -1).filter(i => i !== -1);
    const conclusionAbsIndex = relevantTags.indexOf('2') //node.proofSteps.findIndex((s, i) => tags[node.givens.length + i] === '2') === -1 ? "goals" : "proofSteps";
    if (conclusionAbsIndex === -1) return;
    const [conclusionType, conclusionRelIndex] = absoluteIndexToLocal(node, conclusionAbsIndex);
    nodeActions[conclusionType].addReason(conclusionRelIndex, z3Reason(reasonsIndexes));
    nodeActions[conclusionType].checkReason(conclusionRelIndex);
  }

  return (
    <Modal isOpen={isOpen} onClose={() => { setTags(new Array(100).fill('0')); onClose(); }} size='xl'>
      <ModalOverlay />
      <ModalContent className="iProveModal">
        <ModalHeader>Check correctness of your proof node</ModalHeader>
        <ModalCloseButton />
        <ModalBody>
          <Text>Givens</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.givens.map((s: StatementType, index: number) =>
              <ModalStatement
                statement={s}
                index={index}
                tag={tags[index]}
                setTag={(v: string) => onChange(v, index)}
                isReasonDisabled={isReasonDisabled(index)}
                isConclusionDisabled={true} 
                key={index}/>
            )}
          </div>
          <Text>Proof Steps</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.proofSteps.map((s: StatementType, index: number) =>
              <ModalStatement
                statement={s}
                index={node.givens.length + index}
                tag={tags[node.givens.length + index]}
                setTag={(v: string) => onChange(v, node.givens.length + index)}
                isReasonDisabled={isReasonDisabled(node.givens.length + index)} 
                key={index}/>
            )}
          </div>
          <Text>Goals</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.goals.map((s: StatementType, index: number) =>
              <ModalStatement
                statement={s}
                index={node.givens.length + node.proofSteps.length + index}
                tag={tags[node.givens.length + node.proofSteps.length + index]}
                setTag={(v: string) => onChange(v, node.givens.length + node.proofSteps.length + index)}
                isReasonDisabled={isReasonDisabled(node.givens.length + node.proofSteps.length + index)} 
                key={index}/>
            )}
          </div>
          
        </ModalBody>
        <ModalFooter style={{flexWrap: "wrap"}}>
          <div style={{flexBasis: "100%", textAlign: "right"}}>
          <Button colorScheme='blackAlpha' mr={3} onClick={() => { setTags(new Array(100).fill('0')); onClose(); }}>
            Close
          </Button>
          {checkError ?
              <Tooltip label={renderError(checkError)} fontSize='xs'>
                <Button colorScheme='red' onClick={solveZ3}>Check Again</Button>
              </Tooltip>
              : <Button colorScheme='whatsapp' onClick={solveZ3}>Check</Button>}
          </div>
          <div style={{flexBasis: "100%", textAlign: "right"}}>
            <Text className="errorMessage">{checkError ? renderError(checkError) : ""} </Text>
          </div>
        </ModalFooter>
      </ModalContent>
    </Modal>
  )
}

export default SolveNodeModal;
