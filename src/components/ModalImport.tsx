import { Box, Button, Radio, RadioGroup, Textarea } from '@chakra-ui/react';
import { useEffect, useState } from 'react';
import { display } from "../parser/AST";
import { NodeType } from '../types/Node';
import { StatementType } from '../types/Statement';


/**
 * Modal contents for importing proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalImport = (props: any) => {

    const [textAreaValue, setTextAreaValue] = useState("");

    const parseJSONAddNode = () => {
        // props.addNode();
        console.log(textAreaValue);
    }

    return (
      <Box borderRadius='md' my='1'>
        <div style={{display: 'flex'}}>
            <Textarea
                name="textValue"
                placeholder='Enter Proof'
                size='sm'
                onChange={(e) => {setTextAreaValue(e.target.value)}}
            />        
        </div>
        <div style={{display: 'flex'}}>
            <Button color="blue" onClick={parseJSONAddNode}>Import</Button>
        </div>
      </Box>
)
  }
  
  export default ModalImport;