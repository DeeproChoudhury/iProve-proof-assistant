import { Box, Button } from '@chakra-ui/react';
import { useCallback } from 'react';
import { useIProveStore } from '../../store/store';
import { makeModal } from './makeModal';

/**
 * Modal contents for importing proofs in JSON format
 * 
 * @returns box for modal contents
 */

const ModalAddReasonsInner = () => {
  const actions = useIProveStore(store => store.actions);

  const onYes = useCallback(() => {
    actions.global.hideUI("addReasons");
    actions.global.verifyProofGlobal();
  }, [])

	return (
		<Box borderRadius='md' my='1'>
      Some steps in your proof don't have reasons attached to them.
      Do you want to add the missing reasons automatically?
      <Button variant="outline" colorScheme="blackAlpha" onClick={onYes}>Add Automatically</Button>
      <Button variant="outline" colorScheme="blackAlpha" onClick={() => actions.global.hideUI("addReasons")}>Cancel</Button>
		</Box>
	)
}

const ModalAddReasons = makeModal("addReasons", "Verify Entire Proof", ModalAddReasonsInner);

export default ModalAddReasons;
