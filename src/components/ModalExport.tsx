import { Box, Button, Textarea, useToast } from '@chakra-ui/react';
import { useIProveStore } from '../store/store';

/**
 * Modal contents for Exporting proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalExport = () => {
  const nodes = useIProveStore(store => store.nodes);
  const edges = useIProveStore(store => store.edges);
  const declarations = useIProveStore(store => store.declarations);
  const typeDeclarations = useIProveStore(store => store.typeDeclarations);

  const data = JSON.stringify({
    nodes,
    declarations,
    types: typeDeclarations,
    edges
  })

	/**
	 * Download proof as json file
	 * 
	 * Uses JS implementation
	 * */ 
    const DownloadProof = () => {
		const a = document.createElement("a");
		const file = new Blob([data], { type: "text/plain" });
		a.href = URL.createObjectURL(file);
		a.download = "proof.json";
		a.click();
	}

	/**
     * Box for exporting
     */
   const toast = useToast()
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
                value={data}
                isDisabled
            />
        </div>

        {/* START : Copy to Clipboard Button */}
        <Button variant="outline" colorScheme="blackAlpha" onClick={() => {
          
            navigator.clipboard.writeText(data);
            toast({
              title: 'Copied!',
              description: "Proof has been copied to clipboard",
              status: 'success',
              duration: 5000,
              isClosable: true,
            })
          }} style={{margin: '5px 0'}}>
            Copy to Clipboard
        </Button>
        {/* END : Copy to Clipboard Button */}

		{/* START : Download Proof Button */}
		<Button variant="outline" colorScheme="blackAlpha" onClick={() => {DownloadProof()}} style={{margin: '5px 5px'}}>
			Download Proof
		</Button>
		{/* END : Download Proof Button */}		

      </Box>
    )
  }
  
  export default ModalExport;
