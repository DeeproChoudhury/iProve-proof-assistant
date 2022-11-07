import { Box, Radio, RadioGroup } from '@chakra-ui/react';
import { display } from "../parser/AST";
import { StatementType } from '../types/Statement';


const ModalImport = () => {

    return (
      <Box borderRadius='md' bg='whiteAlpha.300' color='white' my='1'>
        <div style={{display: 'flex'}}>
            <input type="textarea" 
                name="textValue"
            />        
        </div>
      </Box>
    )
  }
  
  export default ModalImport;