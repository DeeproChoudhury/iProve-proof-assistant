import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, Button, Grid, GridItem, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, ModalOverlay, Stack } from '@chakra-ui/react';
import { useState } from 'react';
import ReactFlow, {
  Background, Controls,
} from 'reactflow';
import 'reactflow/dist/style.css';
import Declarations from './Declarations';
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
import TypeDeclarations from './TypeDeclarations';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
} from '@chakra-ui/react'
import {
  Table,
  Thead,
  Tbody,
  Tr,
  Th,
  Td,
  TableContainer,
} from '@chakra-ui/react'
import { renderError } from '../util/errors';
import { SymbolButton } from './SymbolButton';
import { useIProveStore } from '../store/store';

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
  const error = useIProveStore(store => store.error);
  const proofStatus = useIProveStore(store => store.proofStatus);
  const actions = useIProveStore(store => store.actions);


  const [declarationSidebarVisible, setDeclarationSidebarVisible] = useState(true);

  /**
   * Modals
   */
  const [importModalShow, setImportModalShow] = useState(false); // show modal for importing proof (see ModalImport.tsx)
  const [exportModalShow, setExportModalShow] = useState(false); // show modal for exporting proof (see ModalExport.tsx)

  /* Table used to display 'help' information to user */
  const operatorsToSymbols = [{ value: 'and', symbol: '&' },
  { value: 'or', symbol: '||' },
  { value: 'iff', symbol: '<->' },
  { value: 'implies', symbol: '->' },
  { value: 'for all x', symbol: 'FA x.' },
  { value: 'exists x', symbol: 'EX x.' },
  { value: 'negation', symbol: '~' }]

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
      <div className='header'>

        <span className="emBox">
          <span className='highlight'>i</span>Prove
        </span>

        <Stack spacing={4} direction='row' align='center'>

          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={actions.global.addGivenNode}>Add Given</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={actions.global.addGoalNode}>Add Goal</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={actions.global.addProofNode}>Add Proof Node</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={actions.global.addInductionNode}>Add Induction Node</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => { setImportModalShow(true) }}>Import Proofs</Button>
          <Button className="headButton" variant="outline" onClick={() => { setExportModalShow(true) }}>
            Export proof
          </Button>
          <Button className="headButton" variant="outline" onClick={actions.global.verifyProofGlobal}>
            Verify Entire Proof
          </Button>
          <Button className="headButton" variant="outline" onClick={() => { setDeclarationSidebarVisible(!declarationSidebarVisible) }}>
            {declarationSidebarVisible ? "Hide Sidebar" : "Show Sidebar"}
          </Button>


          {/* START: display table mapping symbol to iprove syntax */}
          <Popover>
            <PopoverTrigger>
              <Button className="headButton" variant="outline" >Symbols</Button>
            </PopoverTrigger>
            <PopoverContent style={{ width: "400px" }}>
              <PopoverArrow />
              <PopoverCloseButton />
              <PopoverBody>
                <TableContainer>
                  <Table variant='simple'>
                    <Thead>
                      <Tr>
                        <Th>Logical Operator</Th>
                        <Th>iProve Symbol</Th>
                      </Tr>
                    </Thead>
                    <Tbody>
                      {operatorsToSymbols.map((p, index) => {
                        return <Tr key={index}>
                          <Td>{p.value}</Td>
                          <Td>
                            <SymbolButton symbol={p.symbol} />
                          </Td>
                        </Tr>;
                      }
                      )}
                    </Tbody>
                  </Table>
                </TableContainer>
              </PopoverBody>
            </PopoverContent>
          </Popover>
          {/* END: display table mapping symbol to iProve syntax */}


        </Stack>
      </div>
      {/* END : Header Buttons */}

      {/* START : Proof valid alert */}
      <div className="alert-container">
        {proofStatus === "invalid" && <Alert status='success' className="alert">
          <AlertIcon />
          <AlertTitle>Success!</AlertTitle>
          <AlertDescription>
            Proof is valid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={actions.global.resetProofStatus}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Proof valid alert */}

      {/* START : Proof invalid alert */}
      <div className="alert-container">
        {proofStatus === "invalid" && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof is invalid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={actions.global.resetProofStatus}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Proof invalid alert */}

      {/* START : Error alert */}
      <div className="alert-container">
        {error && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>{error.kind ?? ""} Error!</AlertTitle>
          <AlertDescription>
            {renderError(error)}
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={actions.global.resetError}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Error alert */}

      {/* START : Flow Graph */}
      <div className="flowContainer">

        {/* START : Declarations SideBar */}

        <Grid
          gap={3}
          style={{
            zIndex: 20 /* zIndex to move column to front*/,
            resize: "horizontal",
            overflow: "scroll",
            minWidth: "10vw",
            marginTop: "20vh",
            marginBottom: "10vh",
            marginLeft: "4vw",
            backgroundColor: "#1a29ff4b"

          }}
          visibility={declarationSidebarVisible ? "visible" : "hidden"}
        >

          {/* START : General Declarations */}
          <GridItem style={{ width: "inherit" }}>
            <Declarations />
          </GridItem>
          {/* END : General Declarations */}

          {/* START : Type Declarations */}
          <GridItem style={{ width: "inherit" }}>
            <TypeDeclarations />
          </GridItem>
          {/* END : Type Declarations */}

        </Grid>

        {/* END : Declarations SideBar */}



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
