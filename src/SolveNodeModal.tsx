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
  const [tag, setTags] = useState(new Array(100).fill('0'));

  const onChange = (v: string, index: number) => {
    setTags(tags => tags.map((t, i) => {
      return i === index ? v : t;
    }));
  }

  return (
    <Modal isOpen={isOpen} onClose={() => {setTags(new Array(100).fill('0')); onClose();}}>
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
                tag={tag[index]}
                setTag={(v: string) => onChange(v, index)}/>
            )}
          </div>
          <Text>Proof Steps</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.proofSteps.map((s: StatementType, index: number) =>
              <ModalStatement 
                statement={s} 
                index={node.givens.length + index}
                tag={tag[node.givens.length + index]}
                setTag={(v: string) => onChange(v, node.givens.length + index)}/>
            )}
          </div>
          <Text>Goals</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.goals.map((s: StatementType, index: number) =>
              <ModalStatement 
                statement={s} 
                index={node.givens.length + node.proofSteps.length + index}
                tag={tag[node.givens.length + node.proofSteps.length + index]}
                setTag={(v: string) => onChange(v, node.givens.length + node.proofSteps.length + index)}/>
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