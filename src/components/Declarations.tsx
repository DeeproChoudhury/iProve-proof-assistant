import { AddIcon } from "@chakra-ui/icons";
import { Box, Button, IconButton, Text } from "@chakra-ui/react";
import { ReactNode } from "react";
import Statement from "./Statement";
import { StatementType } from "./TextUpdaterNode";
import './Declarations.css';

export type DeclarationsPropsType = {
  statements: StatementType[];
  updateDeclaration: (index: number, declaration: string) => void;
  addDeclaration: (index: number) => void;
  deleteDeclaration: (index: number) => void;
  checkSyntax: () => void;
}

const Declarations = (props: DeclarationsPropsType) => {
  const { statements, updateDeclaration, addDeclaration, deleteDeclaration, checkSyntax } = props;
  const onChange = (evt: any, updated: number) => {
    updateDeclaration(updated, evt.target.value);
  }
  const checkSyntaxButton: ReactNode = 
    <Button size='xs' colorScheme='blackAlpha' onClick={() => { checkSyntax() }}>Check Syntax</Button>;
  
  return (
    <Box className="declarations">
      <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
        <Text>Declarations</Text>
        <IconButton
          variant='outline'
          aria-label='Add proof step'
          size='xs'
          onClick={() => { addDeclaration(statements.length) }}
          icon={<AddIcon />}
        />
      </div>
      <div style={{ display: 'flex', flexDirection: 'column' }}>
        {statements.map((s: StatementType, index: number) =>
          <Statement
            onChange={e => onChange(e, index)}
            statement={s}
            index={index}
            proofNode={true}
            addAbove={() => { addDeclaration(index) }}
            addBelow={() => { addDeclaration(index + 1) }}
            deleteStatement={() => { deleteDeclaration(index) }} />)}
      </div>
      {checkSyntaxButton}
    </Box>
  )
}

export default Declarations;
