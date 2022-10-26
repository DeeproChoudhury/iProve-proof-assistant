import { StatementType } from "./TextUpdaterNode";
import { Box, Heading, Button, Text, IconButton, useDisclosure } from '@chakra-ui/react';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverFooter,
  PopoverArrow,
  PopoverCloseButton,
  PopoverAnchor,
} from '@chakra-ui/react';
import { ChevronDownIcon } from "@chakra-ui/icons";
import './Statement.css';

export type StatementPropsType = {
  statement: StatementType;
  index?: number;
  onChange: (e: any) => void;
}

const Statement = (props: StatementPropsType) => {
  const {statement, index = 0, onChange} = props;
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
        {/* <PopoverHeader>More options</PopoverHeader> */}
        <PopoverBody style={{display: 'flex', flexDirection: 'column', margin: '10px 0 0 0'}}>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { }} style={{margin: '5px'}}>Add row above</Button>
          <Button size='xs' colorScheme='blackAlpha' onClick={() => { }} style={{margin: '5px'}}>Add row below</Button>
        </PopoverBody>
      </PopoverContent>
    </Popover>

  return (
    <div style={{display: 'flex'}}>
      <input onChange={e => onChange(e)} style={{ marginTop: '5px', flex: '1'}} key={index} value={statement.value} />
      {moreOptions}
    </div>
  )
}

export default Statement;