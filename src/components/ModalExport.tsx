import { CopyIcon, DownloadIcon } from '@chakra-ui/icons';
import { Box, Button, Stack, Textarea, useToast } from '@chakra-ui/react';
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
  const nextNodeId = useIProveStore(store => store.nextNodeId);

  const data = JSON.stringify({
    nodes,
    declarations,
    types: typeDeclarations,
    edges,
    nextNodeId
  })

  /**
   * Download proof as json file
   * 
   * Uses JS implementation
   * */
  const downloadProof = () => {
    const a = document.createElement("a");
    const file = new Blob([data], { type: "text/plain" });
    a.href = URL.createObjectURL(file);
    a.download = "proof.json";
    a.click();
  }

  const copyToClipboard = () => {
    navigator.clipboard.writeText(data);
    toast({
      title: 'Copied!',
      description: "Proof has been copied to clipboard",
      status: 'success',
      duration: 5000,
      isClosable: true,
    })
  }

  const toast = useToast()
  return (
    <Box borderRadius='md' my='1'>
      <div style={{ display: 'flex' }}>
        <Textarea
          name="textValue"
          size='sm'
          focusBorderColor='gray.400'
          background='gray.100'
          textColor='blackAlpha.900'
          _placeholder={{ color: 'gray.400' }}
          value={data}
          isDisabled
        />
      </div>
      <Stack spacing='auto' direction='row' style={{ marginTop: '10px' }}>
        <Button leftIcon={<CopyIcon />} variant="outline" colorScheme="blackAlpha" onClick={copyToClipboard}>
          Copy
        </Button>
        <Button leftIcon={<DownloadIcon />} variant="outline" colorScheme="blackAlpha" onClick={downloadProof}>
          Download
        </Button>
      </Stack>
    </Box>
  )
}

export default ModalExport;
