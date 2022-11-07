import { Box, Button, Radio, RadioGroup, Textarea } from '@chakra-ui/react';
import { useEffect, useState } from 'react';
import { display } from "../parser/AST";
import { NodeData, NodeType } from '../types/Node';
import { StatementType } from '../types/Statement';


/**
 * Modal contents for importing proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalImport = (props: any) => {

    const [textAreaValue, setTextAreaValue] = useState("");

    /**
     * Parse well formed JSON input into node and add to background 
     */
    const parseJSONAddNode = () => {
        const json = JSON.parse(textAreaValue);
        
        console.log(json["type"]);
        props.addNode(json["type"], json["givens"], json["proofs"], json["goals"]);
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