import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, ModalOverlay } from '@chakra-ui/react';
import { useState } from 'react';
import ReactFlow, {
  Background, Controls,
} from 'reactflow';
import 'reactflow/dist/style.css';
import CheckedEdge from './edges/CheckedEdge';
import ImplicationEdge from './edges/ImplicationEdge';
import InvalidEdge from './edges/InvalidEdge';
import './Flow.css';
import ModalExport from './ModalExport';
import ModalImport from './ModalImport';
import GivenNode from './nodes/GivenNode';
import GoalNode from './nodes/GoalNode';
import InductionNode from './nodes/InductionNode';
import ProofNode from './nodes/ProofNode';
import './nodes/ProofNode.css';
import { renderError } from '../util/errors';
import { useIProveStore } from '../store/store';
import Sidebar from './Sidebar';
import Header from './Header';
import Alerts from './Alerts';

const nodeTypes = {
  proofNode: ProofNode,
  givenNode: GivenNode,
  goalNode: GoalNode,
  inductionNode: InductionNode
};
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge };

function Flow() {
  const nodes = useIProveStore(store => store.nodes);
  const edges = useIProveStore(store => store.edges);
  const actions = useIProveStore(store => store.actions);


  const [declarationSidebarVisible, setDeclarationSidebarVisible] = useState(true);

  /**
   * Modals
   */
  const [importModalShow, setImportModalShow] = useState(false); // show modal for importing proof (see ModalImport.tsx)
  const [exportModalShow, setExportModalShow] = useState(false); // show modal for exporting proof (see ModalExport.tsx)


  /**
   * Import Proof given json data. Input list of node data.
   * 
   * @remarks does not need callback?
   */

  return (
    <div style={{ position: 'relative' }}>

      {/* START : Modals */}
      {/* START : Import Modal */}
      <Modal isOpen={importModalShow}
        onClose={() => { setImportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalOverlay />
        <ModalContent className="iProveModal">
          <ModalHeader>Import Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalImport />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Import Modal */}

      {/* START : Export Modal */}
      <Modal isOpen={exportModalShow}
        onClose={() => { setExportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalOverlay />
        <ModalContent className="iProveModal">
          <ModalHeader>Export Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalExport />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Export Modal */}



      {/* START : Header*/}
      <Header 
        sidebarVisible={declarationSidebarVisible} 
        setSidebarVisible={setDeclarationSidebarVisible}
        showExportModal={() => {setExportModalShow(true)}}
        showImportModal={() => {setImportModalShow(true)}}/>
      {/* END : Header Buttons */}

      <Alerts />

      {/* START : Flow Graph */}
      <div className="flowContainer">
        <Sidebar visible={declarationSidebarVisible} />
        <div className="flowCanvas">
          <ReactFlow
            nodes={nodes}
            nodeTypes={nodeTypes}
            edges={edges}
            edgeTypes={edgeTypes}
            disableKeyboardA11y={true} // disable keyboard movemement
            {...actions.flow}
          >
            <Background />
            <Controls position='bottom-right' />
          </ReactFlow>
        </div>
      </div>

    </div>
  );
}

export default Flow;
