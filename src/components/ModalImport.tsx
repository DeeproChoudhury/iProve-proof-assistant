import { Box, Button, Textarea } from '@chakra-ui/react';
import { useState } from 'react';

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
        const importedProof = JSON.parse(textAreaValue);

		// add nodes to graph
        props.addImportedProof(
          importedProof.nodes, 
          importedProof.declarations,
          importedProof.types,
          importedProof.edges,
          importedProof.inductionNodes
        )
    }

    return (
      <Box borderRadius='md' my='1'>
        <div style={{display: 'flex'}}>
            <Textarea
                name="textValue"
                placeholder='Enter Proof'
                size='sm'
                focusBorderColor='gray.400'
                background='gray.100'
                textColor='blackAlpha.900'
                _placeholder={{ color: 'gray.400'}}
                onChange={(e) => {setTextAreaValue(e.target.value)}}
            />        
        </div>
        <Button colorScheme="blackAlpha" onClick={parseJSONAddNode} style={{margin: '5px 0'}}>Import</Button>
      </Box>
	)
}
  
  export default ModalImport;
