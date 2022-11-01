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
import { NodeData, StatementType } from './TextUpdaterNode';
import './SolveNodeModal.css';
import ModalStatement from './ModalStatement';
import Z3Solver from './Solver';
import { ASTNode, ASTSMTLIB2 } from './AST';

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
  
  const localZ3Solver = new Z3Solver.Z3Prover("");
  const solveZ3 = () => {
    const reasons = node.givens.concat(node.proofSteps, node.goals).filter((g, i) => tags[i] === '1')
    const conclusion = node.givens.concat(node.proofSteps, node.goals).find((s, i) => tags[i] === '2')
    console.log('reasons: ' + reasons.map(r => r.value));
    console.log('conclusion: ' + conclusion?.value);
    console.log(reasons.map(x => {
      return ASTSMTLIB2(x.parsed);
    }).join(" "));
    console.log("(not (" + ASTSMTLIB2(conclusion?.parsed) + "))")
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
          <Button colorScheme='whatsapp' onClick={solveZ3}>Check</Button>
        </ModalFooter>
      </ModalContent>
    </Modal>
  )
}

export default SolveNodeModal;