import { Box, Button, Textarea } from '@chakra-ui/react';

/**
 * Modal contents for Exporting proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalExport = (props: { data : string}) => {

	/**
	 * Download proof as json file
	 * 
	 * Uses JS implementation
	 * */ 
    const DownloadProof = () => {
		const a = document.createElement("a");
		const file = new Blob([props.data], { type: "text/plain" });
		a.href = URL.createObjectURL(file);
		a.download = "proof.json";
		a.click();
	}

	/**
     * Box for exporting
     */
    return (
      <Box borderRadius='md' my='1'>
        <div style={{display: 'flex'}}>
            <Textarea
                name="textValue"
                size='sm'
                focusBorderColor='gray.400'
                background='gray.100'
                textColor='blackAlpha.900'
                _placeholder={{ color: 'gray.400'}}
                value={props.data}
                isDisabled
            />
        </div>

        {/* START : Copy to Clipboard Button */}
        <Button colorScheme="blackAlpha" onClick={() => {navigator.clipboard.writeText(props.data)}} style={{margin: '5px 0'}}>
            Copy to Clipboard
        </Button>
        {/* END : Copy to Clipboard Button */}

		{/* START : Download Proof Button */}
		<Button colorScheme="blackAlpha" onClick={() => {DownloadProof()}} style={{marginLeft: '10px'}}>
			Download Proof
		</Button>
		{/* END : Download Proof Button */}		

      </Box>
    )
  }
  
  export default ModalExport;
