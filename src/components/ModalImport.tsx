import { Box, Button, Textarea } from '@chakra-ui/react';
import { useCallback, useState } from 'react';
import { useIProveStore } from '../store/store';

/**
 * Modal contents for importing proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalImport = () => {

  const addImportedProof = useIProveStore(store => store.actions.global.addImportedProof);

  const [textAreaValue, setTextAreaValue] = useState("");

  /**
   * Parse well formed JSON input into node and add to background 
   */
  const parseJSONAddNode = () => {
      const importedProof = JSON.parse(textAreaValue);

	// add nodes to graph
      addImportedProof(
        importedProof 
      )
  }

	// file contents when uploaded
	const [file, setFile] = useState("");

	/**
	 * Upload proof method
	 * 
	 * @returns Box containing form to upload file and upload button to update text area 
	 */
	const UploadProof = useCallback(() => {

		const parseFile = (e : any) => {
			const fileReader = new FileReader();
			fileReader.readAsText(e.target.files[0], "UTF-8");
			
			fileReader.onload = (e : any) => {
				setFile(e.target.result);
				// console.log("e.target.result", file);
			};
		};
		
		return (
			<Box>
				<form id="upload">
					<Button variant="outline" colorScheme="blackAlpha" onClick={() => {setTextAreaValue(file)}} > Upload </Button>
					<input style={{marginLeft: "5px"}} type="file" id="file" accept=".json" onChange={parseFile} />
				</form>		
			</Box>
		);
	}, [file]);

	/**
	 * Modal contents - display proof to be imported/textbox to write proof and 
	 * upload option
	 */
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
				value={textAreaValue}
                onChange={(e) => {setTextAreaValue(e.target.value)}}
            />        
        </div>
        <Button variant="outline" colorScheme="blackAlpha" onClick={parseJSONAddNode} style={{margin: '5px 0'}}>Import</Button>
		<UploadProof/>
	  </Box>
	)
}
  
export default ModalImport;
