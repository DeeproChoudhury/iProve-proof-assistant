import { AddIcon } from "@chakra-ui/icons";
import { Box, Button, IconButton, Text } from "@chakra-ui/react";
import { ReactNode } from "react";
import Statement from "./Statement";
import './TypeDeclarations.css';
import { StatementType } from "../types/Statement";

export type TypesPropsType = {
  statements: StatementType[];
  update: (index: number, declaration: string) => void;
  add: (index: number) => void;
  remove: (index: number) => void;
  checkSyntax: () => void;
  visible: boolean;
}

const TypeDeclarations = (props: TypesPropsType) => {
  const { statements, update, add, remove, checkSyntax, visible } = props;
  const onChange = (evt: any, updated: number) => {
    update(updated, evt.target.value);
  }

  const checkSyntaxButton: ReactNode = 
    <Button size='xs' colorScheme='blackAlpha' onClick={() => { checkSyntax() }}>Check Syntax</Button>;
  return (
    <Box className={"types " + (visible ? 'closed' : 'open')}>
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
        <Text>Types</Text>
        <IconButton
          variant='outline'
          aria-label='Add proof step'
          size='xs'
          onClick={() => { add(statements.length) }}
          icon={<AddIcon />}
        />
      </div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        <Box overflowY="scroll" maxHeight="10em" >
          {statements.map((s: StatementType, index: number) =>
            <Statement
              onChange={e => onChange(e, index)}
              statement={s}
              index={index}
              proofNode={true}
              addAbove={() => { add(index) }}
              addBelow={() => { add(index + 1) }}
              deleteStatement={() => { remove(index) }} />)}  
        </Box>  
      </div>
      {checkSyntaxButton}
    </Box>
  )
}

export default TypeDeclarations;