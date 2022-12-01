import { Box, Button, Textarea } from '@chakra-ui/react';
import { useCallback, useState } from 'react';

/**
 * Modal contents for importing proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalImport = (props: 
	{ 
		addImportedProof : (json: any) => void
	}
) => {

    const [textAreaValue, setTextAreaValue] = useState("");

    /**
     * Parse well formed JSON input into node and add to background 
     */
    const parseJSONAddNode = () => {
        const importedProof = JSON.parse(textAreaValue);

		// add nodes to graph
        props.addImportedProof(
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
			console.log(e);
			const fileReader = new FileReader();
			fileReader.readAsText(e.target.files[0], "UTF-8");
			console.log("here");
			setTextAreaValue(file)
			fileReader.onload = (e : any) => {
				setFile(e.target.result);
				console.log("e.target.result", file);
			};
		};
		
		return (
			<Box style={{display: "inline-block", marginLeft:"10px"}}>
				<form id="upload">
					<Button style = {{padding:"0"}} colorScheme="blackAlpha"><label style={{width:"85px", padding:"0",margin:"0"}} htmlFor="filebtn">Upload</label></Button>
					<input type="file" id="filebtn" accept=".json" onChange={(e) => {parseFile(e)}} hidden />
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
		<div style={{marginTop : "5px"}}>
			<Button colorScheme="blackAlpha" onClick={parseJSONAddNode} style={{display: "inline-block"}}>Import</Button>
			<UploadProof/>
		</div>
	  </Box>
	)
}
  
export default ModalImport;
