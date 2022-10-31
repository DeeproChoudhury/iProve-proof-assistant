import React, { useState } from 'react';
import {
  Modal,
  ModalOverlay,
  ModalContent,
  ModalHeader,
  ModalFooter,
  ModalBody,
  ModalCloseButton,
  Text,
  Button,
} from '@chakra-ui/react';
import { NodeData, ProofNodeTypes, StatementType } from './TextUpdaterNode';
import './SolveNodeModal.css';
import ModalStatement from './ModalStatement';
import { Radio, RadioGroup, Stack } from '@chakra-ui/react'

export type SolveNodeModalPropsType = {
  isOpen: boolean,
  onClose: () => void,
  node: NodeData,
}

const SolveNodeModal = (props: SolveNodeModalPropsType) => {
  const { isOpen, onClose, node} = props;
  const [tags, setTags] = useState(new Array(100).fill('0'));

  const onChange = (v: string, index: number) => {
    setTags(tags => tags.map((t, i) => {
      if (t == '2' && v === '2') {
        return '0';
      }
      if (i === index) {
        return v;
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

  return (
    <Modal isOpen={isOpen} onClose={() => {setTags(new Array(100).fill('0')); onClose();}} size='xl'>
      <ModalOverlay />
      <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
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
                isConclusionDisabled={true}/>
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
                isReasonDisabled={isReasonDisabled(node.givens.length + index)}/>
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
                isReasonDisabled={isReasonDisabled(node.givens.length + node.proofSteps.length + index)}/>
            )}
          </div>
        </ModalBody>

        <ModalFooter>
          <Button colorScheme='blackAlpha' mr={3} onClick={() => {setTags(new Array(100).fill('0')); onClose();}}>
            Close
          </Button>
          <Button colorScheme='whatsapp'>Check</Button>
        </ModalFooter>
      </ModalContent>
    </Modal>
  )
}

export default SolveNodeModal;