import { Box, Button, Textarea } from '@chakra-ui/react';

/**
 * Modal contents for Exporting proofs in JSON format
 * 
 * @returns box for modal contents
 */
const ModalExport = (props: any) => {

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
        <Button colorScheme="blackAlpha" onClick={() => {navigator.clipboard.writeText(props.data)}} style={{margin: '5px 0'}}>
            Copy to Clipboard
        </Button>
      </Box>
    )
  }
  
  export default ModalExport;
