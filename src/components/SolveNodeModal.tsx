import {
  Button, Modal, ModalBody,
  ModalCloseButton, ModalContent, ModalFooter, ModalHeader, ModalOverlay, Text, Tooltip
} from '@chakra-ui/react';
import { useState } from 'react';
import { ASTSMTLIB2, isTerm } from '../parser/AST';
import Z3Solver from '../solver/Solver';
import { NodeData } from '../types/Node';
import { StatementType } from '../types/Statement';
import { z3Reason } from '../util/reasons';
import { statementToZ3 } from '../util/statements';
import ModalStatement from './ModalStatement';
import './SolveNodeModal.css';

export type SolveNodeModalPropsType = {
  isOpen: boolean,
  onClose: () => void,
  node: NodeData,
}

const SolveNodeModal = (props: SolveNodeModalPropsType) => {
  const { isOpen, onClose, node } = props;
  const [tags, setTags] = useState(new Array(100).fill('0'));
  const [checkFailed, setCheckFailed] = useState(false);

  const onChange = (v: string, index: number) => {
    setTags(tags => tags.map((t, i) => {
      if (t === '2' && v === '2') {
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
    const reasonsIndexes = node.givens.concat(node.proofSteps, node.goals).map((g, i) => tags[i] === '1' ? i : -1).filter((i) => i >= 0)
    const reasons = node.givens.concat(node.proofSteps, node.goals).filter((g, i) => tags[i] === '1')
    const conclusionType = node.proofSteps.findIndex((s, i) => tags[node.givens.length + i] === '2') === -1 ? "goals" : "proofSteps";
    const conclusionIndex = conclusionType === "proofSteps" ?
      node.proofSteps.findIndex((s, i) => tags[node.givens.length + i] === '2') :
      node.goals.findIndex((s, i) => tags[node.givens.length + node.proofSteps.length + i] === '2');
    const conclusion = conclusionType === "proofSteps" ? node.proofSteps[conclusionIndex] : node.goals[conclusionIndex];
    if (reasons.some(r => !r.parsed) || !conclusion.parsed) {
      setCheckFailed(true);
      return;
    }
    const declarations = node.declarationsRef.current.map(statementToZ3).join("\n");
    const smtReasons = reasons.map(reason => {
      const reasonStr = statementToZ3(reason);
      if (!reason.parsed) return "";
      if (isTerm(reason.parsed)) return `(assert ${reasonStr})`;
      else return reasonStr;
    }).join("\n");
    console.log(declarations);
    console.log(smtReasons);
    const smtConclusion = "(assert (not " + ASTSMTLIB2(conclusion.parsed) + "))";
    console.log(smtConclusion);
    localZ3Solver.solve(declarations + "\n" + smtReasons + "\n" + smtConclusion + "\n (check-sat)").then((output: string) => {
      if (output === "unsat\n") {
        node.thisNode[conclusionType].addReason(conclusionIndex, z3Reason(reasonsIndexes));
        setCheckFailed(false);
      } else {
        node.thisNode[conclusionType].removeReason(conclusionIndex);
        setCheckFailed(true);
      }
    })
  }

  return (
    <Modal isOpen={isOpen} onClose={() => { setTags(new Array(100).fill('0')); onClose(); }} size='xl'>
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

        <ModalFooter>
          <Button colorScheme='blackAlpha' mr={3} onClick={() => { setTags(new Array(100).fill('0')); onClose(); }}>
            Close
          </Button>
          {checkFailed ?
              <Tooltip label='Invalid proof! Please try again.' fontSize='xs'>
                <Button colorScheme='red' onClick={solveZ3}>CheckAgain</Button>
              </Tooltip> :
              <Button colorScheme='whatsapp' onClick={solveZ3}>Check</Button>}
        </ModalFooter>
      </ModalContent>
    </Modal>
  )
}

export default SolveNodeModal;
