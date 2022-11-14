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
} from '@chakra-ui/react';
import { ChevronDownIcon,CheckIcon } from "@chakra-ui/icons";
import './Statement.css';
import { useRef, useState } from "react";
import { display } from "../parser/AST";
import { StatementType } from '../types/Statement';

export type StatementPropsType = {
  statement: StatementType;
  index?: number;
  onChange: (e: any) => void;
  proofNode?: boolean;
  addAbove?: () => void;
  addBelow?: () => void;
  deleteStatement?: () => void;
}

const Statement = (props: StatementPropsType) => {
  const input = useRef<HTMLInputElement>(null);
  const {statement, index = 0, onChange, addAbove = () => {}, addBelow = () => {}, deleteStatement = () => {}, proofNode = false} = props;
  const { isOpen, onOpen, onClose } = useDisclosure();
  const [isFocused, setFocused] = useState<boolean>(false);
  const onFocus = () => setFocused(true);
  const onBlur = () => setFocused(false);

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
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {addAbove(); onClose();}} style={{margin: '5px'}}>Add row above</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {addBelow(); onClose();}} style={{margin: '5px'}}>Add row below</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => {deleteStatement(); onClose();}} style={{margin: '5px'}}>Delete this row</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>

  const inputStyle = "statement-input" + (statement.syntaxCorrect === false ? " syntax-error" : "") 
  const value = statement.parsed && !isFocused ? display(statement.parsed) : statement.value;
  const reasonsLabel = statement.reason && (statement.reason.dependencies.length === 0 ? 'lemma' : `from ${statement.reason.dependencies.map(r => `(${r + 1})`).join(", ")}`)

  return (
    <div style={{display: 'flex'}}>
      <div style={{margin: 'auto 5px'}}>({index + 1})</div>
      <input ref={input} onFocus={onFocus} onBlur={onBlur} onChange={e => onChange(e)} className={inputStyle} style={{ marginTop: '5px', flex: '1'}} key={index} value={value} />
      {statement.reason && <Tooltip label={reasonsLabel} fontSize='xs'>
        <CheckIcon style={{margin: 'auto 5px'}}/>
      </Tooltip>}
      {moreOptions}
    </div>
  )
}

export default Statement;
