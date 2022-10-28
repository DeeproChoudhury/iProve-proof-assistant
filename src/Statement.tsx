import { StatementType } from "./TextUpdaterNode";
import { Button, IconButton, useDisclosure } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
} from '@chakra-ui/react';
import { ChevronDownIcon } from "@chakra-ui/icons";
import './Statement.css';
import { useRef, useState } from "react";
import { display } from "./AST";

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
  console.log(statement.parsed)
  const value = statement.parsed && !isFocused ? display(statement.parsed) : statement.value;

  return (
    <div style={{display: 'flex'}}>
      <input ref={input} onFocus={onFocus} onBlur={onBlur} onChange={e => onChange(e)} className={inputStyle} style={{ marginTop: '5px', flex: '1'}} key={index} value={value} />
      {proofNode && moreOptions}
    </div>
  )
}

export default Statement;
