import { AttachmentIcon, ExternalLinkIcon } from '@chakra-ui/icons';
import { Box, Button, Input, Stack, Textarea } from '@chakra-ui/react';
import { useRef, useState } from 'react';
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
	const parseJSONAddNode = () => addImportedProof(textAreaValue);

	// file contents when uploaded
	// const [file, setFile] = useState("");
	const inputRef = useRef<HTMLInputElement | null>(null)
	const handleClick = () => inputRef.current?.click()
	const parseFile = (e: any) => {
		const fileReader = new FileReader();
		fileReader.readAsText(e.target.files[0], "UTF-8");

		fileReader.onload = (e: any) => {
			// setFile(e.target.result);
			setTextAreaValue(e.target.result)
			// console.log("e.target.result", file);
		};

	};

	/**
	 * Modal contents - display proof to be imported/textbox to write proof and 
	 * upload option
	 */
	return (
		<Box borderRadius='md' my='1'>
			<div style={{ display: 'flex' }}>
				<Textarea
					name="textValue"
					placeholder='Enter Proof'
					size='sm'
					focusBorderColor='gray.400'
					background='gray.100'
					textColor='blackAlpha.900'
					_placeholder={{ color: 'gray.400' }}
					value={textAreaValue}
					onChange={(e) => { setTextAreaValue(e.target.value) }}
				/>
			</div>
			<Stack spacing='auto' direction='row' style={{marginTop: '10px'}}>
				<div onClick={handleClick}>
					<Input type="file" accept='.json' onChange={parseFile} id='file' hidden ref={(e) => {
							inputRef.current = e
						}}></Input>
					<Button leftIcon={<AttachmentIcon />} variant="outline" colorScheme="blackAlpha">
						Upload
					</Button>
				</div>
				<Button leftIcon={<ExternalLinkIcon />} variant="outline" colorScheme="blackAlpha" onClick={parseJSONAddNode}>
					Import
				</Button>
			</Stack>
		</Box>
	)
}

export default ModalImport;
