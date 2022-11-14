import { Button, IconButton, useDisclosure } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
  Tooltip,
  Text,
} from '@chakra-ui/react';
import { ChevronDownIcon,CheckIcon } from "@chakra-ui/icons";
import './Statement.css';
import { useRef, useState } from "react";
import { Assumption, display, VariableDeclaration } from "../parser/AST";
import { StatementType } from '../types/Statement';

export type StatementPropsType = {
  statement: StatementType;
  index?: number;
  onChange: (e: any) => void;
  proofNode?: boolean;
  addAbove?: (wrappers?: (VariableDeclaration | Assumption)[]) => void;
  addBelow?: (wrappers?: (VariableDeclaration | Assumption)[]) => void;
  deleteStatement?: () => void;
  setWrappers?: () => void;
}

const Statement = (props: StatementPropsType) => {
  const input = useRef<HTMLInputElement>(null);
  const {statement, index = 0, onChange, addAbove = () => {}, addBelow = () => {}, deleteStatement = () => {}, proofNode = false, setWrappers = () => {}} = props;
  const { isOpen, onOpen, onClose } = useDisclosure();
  const [isFocused, setFocused] = useState<boolean>(false);
  const onFocus = () => setFocused(true);
  const onBlur = () => {setFocused(false); setWrappers()};
  const belowWrappers = statement.parsed?.kind === "VariableDeclaration" ? [...statement.wrappers, statement.parsed] : statement.wrappers;
  
  /**
   * Popout for adding/deleting statement lines
   */
  const moreOptions = 
    <Popover isOpen={isOpen} onClose={onClose}>
      <PopoverTrigger>
        <IconButton
          variant='outline'
          aria-label='More options'
          size='xs'
          icon={<ChevronDownIcon />}
          onClick={onOpen}
          style={{margin: '5px 0 5px 5px'}}
        />
      </PopoverTrigger>
      <PopoverContent style={{width: '150px'}}>
        <PopoverArrow />
        <PopoverCloseButton />
        <PopoverHeader>More options</PopoverHeader>
        <PopoverBody style={{display: 'flex', flexDirection: 'column'}}>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {addAbove(statement.wrappers); onClose();}} style={{margin: '5px'}}>Add row above</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {addBelow(belowWrappers); onClose();}} style={{margin: '5px'}}>Add row below</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {deleteStatement(); onClose();}} style={{margin: '5px'}}>Delete this row</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>

    
  console.log(statement.wrappers);
  const inputStyle = "statement-input" + (statement.syntaxCorrect === false ? " syntax-error" : "") 
  const value = statement.parsed && !isFocused ? display(statement.parsed) : statement.value;
  const indentSize = 15 * statement.wrappers.length;
  const reasonsLabel = statement.reason && (statement.reason.dependencies.length === 0 ? 'lemma' : `from ${statement.reason.dependencies.map(r => `(${r + 1})`).join(", ")}`)
  return (
    <div style={{display: 'flex', marginLeft: `${indentSize}px` }}>
      <Text fontSize="sm" style={{margin: 'auto 5px', width: '30px'}}>({index + 1})</Text>
      <input ref={input} onFocus={onFocus} onBlur={onBlur} onChange={e => onChange(e)} className={inputStyle} style={{ marginTop: '5px', flex: '1'}} key={index} value={value} />
      {statement.reason && <Tooltip label={reasonsLabel} fontSize='xs'>
        <CheckIcon style={{margin: 'auto 5px'}}/>
      </Tooltip>}
      {moreOptions}
    </div>
  )
}

export default Statement;
