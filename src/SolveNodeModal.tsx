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
  const { isOpen, onClose, node } = props;

  return (
    <Modal isOpen={isOpen} onClose={onClose}>
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
                index={index} />
            )}
          </div>
          <Text>Proof Steps</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.proofSteps.map((s: StatementType, index: number) =>
              <ModalStatement 
                statement={s} 
                index={node.givens.length + index}/>
            )}
          </div>
          <Text>Goals</Text>
          <div style={{ display: 'flex', flexDirection: 'column' }}>
            {node.goals.map((s: StatementType, index: number) =>
              <ModalStatement 
                statement={s} 
                index={node.givens.length + node.proofSteps.length + index}/>
            )}
          </div>
        </ModalBody>

        <ModalFooter>
          <Button colorScheme='blackAlpha' mr={3} onClick={onClose}>
            Close
          </Button>
          <Button colorScheme='whatsapp'>Check</Button>
        </ModalFooter>
      </ModalContent>
    </Modal>
  )
}

export default SolveNodeModal;