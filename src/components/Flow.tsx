import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, Button, Grid, GridItem, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, Stack } from '@chakra-ui/react';
import { useCallback, useMemo, useRef, useState } from 'react';
import ReactFlow, {
  Background, Controls, Edge, Node
} from 'reactflow';
import 'reactflow/dist/style.css';
import { makeDeclarationCallbacks } from '../callbacks/declarationsCallbacks';
import { makeFlowCallbacks } from '../callbacks/flowCallbacks';
import { makeInductionNodeCallbacks } from '../callbacks/inductionNodeCallbacks';
import { makeNodeCallbacks } from '../callbacks/nodeCallbacks';
import Z3Solver from '../logic/Solver';
import { ErrorLocation, IProveError } from '../types/ErrorLocation';
import { AnyNodeType, InductionNodeType, NodeKind, StatementNodeType } from '../types/Node';
import { StatementType } from '../types/Statement';
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
import { allParsed, internalsStatus } from '../util/nodes';
import { SymbolButton } from './SymbolButton';

const nodeTypes = {
  proofNode: ProofNode,
  givenNode: GivenNode,
  goalNode: GoalNode,
  inductionNode: InductionNode
};
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge };

function Flow() {
  const [proofValid, setProofValid] = useState(false);

  const [nodes, setNodes] = useState<AnyNodeType[]>([]);


  const [edges, setEdges] = useState<Edge[]>([]);
  const [count, setCount] = useState(0);
  const [error, setError] = useState<IProveError | undefined>(undefined);
  const [stopGlobalCheck, setStopGlobalCheck] = useState<boolean | undefined>(undefined);
  const [declarations, setDeclarations] = useState<StatementType[]>([]);
  const [declarationSidebarVisible, setDeclarationSidebarVisible] = useState(true);

  const [typeDeclarations, setTypeDeclarations] = useState<StatementType[]>([]);
  const localZ3Solver = useMemo(() => new Z3Solver.Z3Prover(""), []);

  /**
   * Modals
   */
  const [importModalShow, setImportModalShow] = useState(false); // show modal for importing proof (see ModalImport.tsx)
  const [exportModalShow, setExportModalShow] = useState(false); // show modal for exporting proof (see ModalExport.tsx)

  // update refs everytime this hook runs
  const nodesRef = useRef(nodes);
  nodesRef.current = nodes;
  const edgesRef = useRef(edges);
  edgesRef.current = edges;
  const declarationsRef = useRef(declarations);
  declarationsRef.current = declarations;
  const typeDeclarationsRef = useRef(typeDeclarations);
  typeDeclarationsRef.current = typeDeclarations;

  const nextId = useCallback(() => {
    setCount(count + 1);
    return count;
  }, [count]);

  const checkProofValid = (ns: Node[], es: Edge[]): void => {
    const givens = ns.filter(node => node.type === "givenNode");
    const goals = ns.filter(node => node.type === "goalNode");
    setProofValid(checkValid(ns, goals, givens, es, []));
  }

  const checkValid = (ns: Node[], currs: Node[], givens: Node[], es: Edge[], visited: Node[]): boolean => {
    // check that all paths into goals eventually start at givens and only use valid edges and do not cycle
    const non_given_currs = currs.filter(node => !givens.includes(node));
    const cycle_found = non_given_currs.some(n => visited.includes(n)); //check if any current node has already been found
    if (cycle_found) {
      console.log("here3");
      return false;
    }
    const new_visited = visited.concat(non_given_currs);
    const non_given_currs_ids = non_given_currs.map(node => node.id);
    if (non_given_currs_ids.length === 0) {
      return true
    }
    const valid_edges_to_non_given_currs: Edge[] = es.filter(e => non_given_currs_ids.includes(e.target));
    const prev_ids = valid_edges_to_non_given_currs.map(e => e.source);
    const hit_currs = valid_edges_to_non_given_currs.map(e => e.target);
    const no_incoming_edges_non_givens = non_given_currs_ids.filter(id => !hit_currs.includes(id));
    if (no_incoming_edges_non_givens.length > 0) {
      console.log("here2");
      return false; //path can't end at a non_given node
    }
    const prev_nodes = ns.filter(node => prev_ids.includes(node.id));
    if (prev_nodes.length === 0) {
      console.log("here1");
      return false;
    } else {
      return checkValid(ns, prev_nodes, givens, es, new_visited);
    }
  }

  /* Table used to display 'help' information to user */
  const operatorsToSymbols = [{ value: 'and', symbol: '&' },
  { value: 'or', symbol: '|' },
  { value: 'iff', symbol: '<->' },
  { value: 'implies', symbol: '->' },
  { value: 'for all x', symbol: 'FA x.' },
  { value: 'exists x', symbol: 'E x.' },
  { value: 'negation', symbol: '~'} ]

  const makeThisNode = useMemo(() => makeNodeCallbacks(nodesRef, edgesRef, declarationsRef, setNodes, setEdges, setError, setStopGlobalCheck, localZ3Solver), [localZ3Solver]);
  const makeThisInductionNode = useMemo(() => makeInductionNodeCallbacks(nodesRef, edgesRef, declarationsRef, setNodes, setEdges, setError, localZ3Solver), [localZ3Solver]);

  const declarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setDeclarations, setError), []);
  const typeDeclarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setTypeDeclarations, setError), []);

  const flowCallbacks = useMemo(() => makeFlowCallbacks(nodes, setNodes, setEdges, declarationsRef, nextId, makeThisNode), [nodes, nextId, makeThisNode]);

  const addNode = useCallback((nodeType: NodeKind) => {
    const count = nextId();
    console.log(nodes);

    if (nodeType === "inductionNode") {
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          internalsStatus: "unchecked",
          edgesStatus: "unchecked",
          types: [{ value: '', wrappers: [] }],
          identifier: [{ value: '', wrappers: [] }],
          inductiveCases: [],
          baseCases: [],
          motive: [{ value: '', wrappers: [] }],
          declarationsRef,
          typeDeclarationsRef,
          thisNode: makeThisInductionNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: 'inductionNode',
      }]);
    }
    else {
      const blankStatement = { value: '', wrappers: [] };
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          edgesStatus: "unchecked",
          givens: [],
          proofSteps: [],
          goals: nodeType !== 'goalNode' ? [blankStatement] : [],
          declarationsRef,
          thisNode: makeThisNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: nodeType,
      }]);
    }

  }, [nextId, makeThisNode, makeThisInductionNode]);


  /**
   * Import Proof given json data. Input list of node data.
   * 
   * @remarks does not need callback?
   */
  const addImportedProof = useCallback((json: any) => {
    // Create Given, Proof, Goal Nodes from input data
    const nodeData = json.nodes.map((node: any) => {
      const id = node.id;
      setCount(Math.max(count, id) + 1);

      if (node.type === "inductionNode") {
        return {
          id: `${id}`,
          data: {
            label: node.data.label,
            allParsed: false,
            internalsValid: false,
            edgesValid: true,
            // predicate: node.data.predicate,
            declarationsRef,
            // inductiveHypotheses: node.data.inductiveHypotheses,
            typeDeclarationsRef,
            types: node.data.types,
            thisNode: makeThisInductionNode(`${id}`),

            inductiveCases: node.data.inductiveCases,
            baseCases: node.data.baseCases,
            motive: node.data.motive,

          },
          position: node.position,
          type: node.type,
        }
      } else {
        return {
          id: `${id}`,
          data: {
            label: node.data.label,
            givens: node.data.givens,
            proofSteps: node.data.proofSteps,
            goals: node.data.goals,
            declarationsRef,
            thisNode: makeThisNode(`${id}`)
          },
          position: node.position,
          type: node.type,
        }
      }
    });
    
    setDeclarations(json.declarations);
    setTypeDeclarations(json.types);
    setNodes(nodeData);
    setEdges(json.edges);

  }, [makeThisNode]);

  const verifyProofGlobal = async () => {

    nodes.forEach(node => {
      node.data.thisNode.parseAll()
      node.data.thisNode.checkInternal();
      node.data.thisNode.checkEdges();
    });
    setNodes(nodes => {
      const allValid = nodes.every(node => allParsed(node) && internalsStatus(node) === "valid" && node.data.edgesStatus === "valid");
      console.log(allValid);
      return nodes;
      // TODO: check connections
    });
  }

  return (
    <div style={{ position: 'relative' }}>

      {/* START : Modals */}
      {/* START : Import Modal */}
      <Modal isOpen={importModalShow}
        onClose={() => { setImportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
          <ModalHeader>Import Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalImport addImportedProof={addImportedProof} />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Import Modal */}

      {/* START : Export Modal */}
      <Modal isOpen={exportModalShow && proofValid}
        onClose={() => { setExportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
          <ModalHeader>Export Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalExport data={
              JSON.stringify({
                nodes: nodes,
                declarations: declarations,
                types: typeDeclarations,
                edges: edges,
              })
            } />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Export Modal */}

      {/* START : Export alert */}
      <div className="alert-container">
        {exportModalShow && !proofValid && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof can not be printed as proof is not valid.
            For a proof graph to be valid, all paths into goal nodes must start at a given node,
            only use valid edges and be acyclical.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setExportModalShow(false) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Export alert */}


      {/* START : Proof valid alert */} 
      <div className="alert-container">
        {stopGlobalCheck === false && <Alert status='success' className="alert">
          <AlertIcon />
          <AlertTitle>Success!</AlertTitle>
          <AlertDescription>
            Proof is valid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setStopGlobalCheck(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Proof valid alert */} 

      {/* START : Error alert */} 
      <div className="alert-container">
        {error && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>{error.kind ?? ""} Error!</AlertTitle>
          <AlertDescription>
            { renderError(error) }
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setError(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Error alert */}

      {/* START : Header Buttons */}
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('givenNode')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goalNode')}>Add Goal</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('proofNode')}>Add Proof Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('inductionNode')}>Add Induction Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => { setImportModalShow(true) }}>Import Proofs</Button>
          <Button onClick={() => { checkProofValid(nodes, edges); setExportModalShow(true) }}>
            Export proof
          </Button>
          <Button onClick={() => { verifyProofGlobal() }}>
            Verify Entire Proof
          </Button>
          <Button onClick={() => { setDeclarationSidebarVisible(!declarationSidebarVisible) }}>
            {declarationSidebarVisible ? "Hide Sidebar" : "Show Sidebar"}
          </Button>


          {/* START: display table mapping symbol to iprove syntax */}
          <Popover>
            <PopoverTrigger>
              <Button>Symbols</Button>
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
                      {operatorsToSymbols.map((p, index) =>
                        {
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


      {/* START : Flow Graph */}
      <div style={{ display: 'flex', flexDirection: 'row', height: "100vh" }}>
        {/* START : Column for declarations */}
        <Grid style={{ zIndex: 20 /* zIndex to move column to front*/ }}
          // templateRows='repeat(3, 1fr)'
          gap={3}
          visibility={declarationSidebarVisible ? "visible" : "hidden"}
        >

          {/* START : General Declarations */}
          <GridItem >
            <Declarations
              statements={declarations}
              {...declarationsCallbacks}
              visible={true} />
          </GridItem>
          {/* END : General Declarations */}

          {/* START : Type Declarations */}
          <GridItem>
            <TypeDeclarations
              statements={typeDeclarations}
              {...typeDeclarationsCallbacks}
              visible={true} />
          </GridItem>
          {/* END : Type Declarations */}

        </Grid>
        {/* END : Column for declarations */}


        <div style={{ height: '85vh', width: '100%' }}>
          <ReactFlow
            nodes={(nodes)}
            nodeTypes={nodeTypes}
            edges={edges}
            edgeTypes={edgeTypes}
            disableKeyboardA11y={true} // disable keyboard movemement
            {...flowCallbacks}
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
