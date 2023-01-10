import { Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, ModalOverlay } from "@chakra-ui/react";
import { ComponentType } from "react";
import { UIComponentName, useIProveStore } from "../../store/store";

export const makeModal = (name: UIComponentName, title: string, ModalInner: ComponentType) => () => {
  
  const isOpen = useIProveStore(store => store.uiShown[name]);
  const hideUI = useIProveStore(store => store.actions.global.hideUI);

  return (<Modal isOpen={isOpen}
    onClose={() => hideUI(name) }        // onAfterOpen={() => {}}
    >
    <ModalOverlay />
    <ModalContent className="iProveModal">
      <ModalHeader>{title}</ModalHeader>
      <ModalCloseButton />
      <ModalBody>
        <ModalInner />
      </ModalBody>
    </ModalContent>
  </Modal>)
}
