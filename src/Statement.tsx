import { StatementType } from "./TextUpdaterNode";
import { background, Button, IconButton, useDisclosure } from '@chakra-ui/react';
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
  const {statement, index = 0, onChange, addAbove = () => {}, addBelow = () => {}, deleteStatement = () => {}, proofNode = false} = props;
  const { isOpen, onOpen, onClose } = useDisclosure();

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

  return (
    <div style={{display: 'flex'}}>
      <input onChange={e => onChange(e)} className={inputStyle} style={{ marginTop: '5px', flex: '1'}} key={index} value={statement.value} />
      {proofNode && moreOptions}
    </div>
  )
}

export default Statement;