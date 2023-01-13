import { useRef, useState } from 'react';
import { Button, IconButton, useDisclosure, Input, Textarea } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
  Text,
} from '@chakra-ui/react';
import { ChevronDownIcon } from "@chakra-ui/icons";
import './Statement.css';
import { display } from "../util/trees";
import { StatementType } from '../types/Statement';
import ReasonIndicator from './ReasonIndicator';
import TextareaAutosize from 'react-textarea-autosize';

export type StatementPropsType = {
  statement: StatementType;
  index?: number;
  onChange: (e: any) => void;
  addable?: boolean;
  addAbove?: () => void;
  addBelow?: () => void;
  removeReason?: () => void;
  deleteStatement?: () => void;
  afterEdit?: () => void;
  setWrappers?: () => void;
}

const Statement = (props: StatementPropsType) => {
  const input = useRef<HTMLTextAreaElement>(null);
  const {
    statement,
    index = 0,
    onChange,
    addAbove = () => {},
    addBelow = () => {},
    removeReason = undefined,
    deleteStatement = () => {},
    addable: addable = true,
    afterEdit = () => {},
    setWrappers = () => {}
  } = props;
  const { isOpen, onOpen, onClose } = useDisclosure();
  const [isFocused, setFocused] = useState<boolean>(false);
  const [oldValue, setOldValue] = useState<string>("");
  const onFocus = () => {
    setFocused(true);
    setOldValue(statement.value);
  };
  const onBlur = () => {
    setFocused(false);
    if (statement.value !== oldValue) afterEdit();
  };
  
  /**
   * Popout for adding/deleting statement lines
   */
  const MoreOptions = () => {
    return (
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
            {removeReason && <Button size='xs' colorScheme='blackAlpha' onClick={() => {removeReason(); onClose();}} style={{margin: '5px'}}>Clear reason</Button>}
            <Button size='xs' colorScheme='blackAlpha' onClick={() => {deleteStatement(); onClose();}} style={{margin: '5px'}}>Delete this row</Button>
          </PopoverBody>
        </PopoverContent>
      </Popover>  
    )
  }
    

  const inputStyle = "statement-input" + (statement.syntaxCorrect === false ? " syntax-error" : "") 
  const value = statement.parsed && !isFocused ? display(statement.parsed) : statement.value;
  const indentSize = 15 * statement.wrappers.length;
  return (
    <div className="nodrag" style={{display: 'flex', marginLeft: `${indentSize}px` }} key={`statement-${index}`}>
      <Text fontSize="sm" style={{margin: 'auto 5px', width: '30px'}}>({index + 1})</Text>
      <TextareaAutosize
        //size="lg"
        ref={input}
        onFocus={onFocus}
        onBlur={onBlur}
        onChange={e => onChange(e)}
        className={inputStyle}
        style={{ marginTop: '5px', flex: '1', backgroundColor: "rgb(252, 248, 242)" }}
        key={index}
        rows={1}
        //variant="unstyled"
        //resize="vertical"
        value={value} />
      {statement.reason && <ReasonIndicator reason={statement.reason} />}
      {addable ? <MoreOptions /> : <></>}
    </div>
  )
}

export default Statement;
