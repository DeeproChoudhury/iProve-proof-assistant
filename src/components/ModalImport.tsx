import { Box, Button, Radio, RadioGroup, Textarea } from '@chakra-ui/react';
import { display } from "../parser/AST";
import { StatementType } from '../types/Statement';


const ModalImport = () => {

    return (
      <Box borderRadius='md' my='1'>
        <div style={{display: 'flex'}}>
            <Textarea
                name="textValue"
                placeholder='Enter Proof'
                size='sm'
            />        
        </div>
        <div style={{display: 'flex'}}>
            <Button color="blue">Import</Button>
        </div>
      </Box>
)
  }
  
  export default ModalImport;