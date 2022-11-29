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
import Z3Solver from '../solver/Solver';
import { ErrorLocation } from '../types/ErrorLocation';
import { InductionNodeType, NodeType, StatementNodeType } from '../types/Node';
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

const nodeTypes = {
  proofNode: ProofNode,
  givenNode: GivenNode,
  goalNode: GoalNode,
  inductionNode: InductionNode
};
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge };

function Flow() {
  const [proofValid, setProofValid] = useState(false);

  const [nodes, setNodes] = useState<StatementNodeType[]>([]);
  const [inductionNodes, setInductionNodes] = useState<InductionNodeType[]>([]);


  const [edges, setEdges] = useState<Edge[]>([]);
  const [count, setCount] = useState(0);
  const [error, setError] = useState<ErrorLocation | undefined>(undefined);
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
  const inductionNodesRef = useRef(inductionNodes);
  inductionNodesRef.current = inductionNodes;
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
  const makeThisInductionNode = useMemo(() => makeInductionNodeCallbacks(inductionNodesRef, edgesRef, declarationsRef, setInductionNodes, setEdges, setError, localZ3Solver), [localZ3Solver]);

  const declarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setDeclarations, setError), []);
  const typeDeclarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setTypeDeclarations, setError), []);

  const flowCallbacks = useMemo(() => makeFlowCallbacks(nodes, inductionNodes, setNodes, setInductionNodes, setEdges, declarationsRef, nextId, makeThisNode), [nodes, inductionNodes, nextId, makeThisNode]);

  const addNode = useCallback((nodeType: NodeType) => {
    const count = nextId();

    if (nodeType === "inductionNode") {
      setInductionNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          types: [{ value: '', wrappers: [] }],
          predicate: [{ value: '', wrappers: [] }],
          inductiveCases: [],
          baseCases: [],
          inductiveHypotheses: [{ value: '', wrappers: [] }],
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
          givens: nodeType === 'goalNode' ? [blankStatement] : [],
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


  const addImportedProof = useCallback((jsonNodes: any[], jsonDeclarations: any[], jsonTypes: any[], jsonEdges: any[], jsonInduction: any[]) => {
    const nodeData = jsonNodes;
    const declarationsData = jsonDeclarations.map(d => {
      return {
        value: d,
        wrappers: []
      }
    });
    const typeDeclarations = jsonTypes.map(t => {
      return {
        value: t,
        wrappers: []
      }
    });

    console.log(jsonEdges);
    // const edges = jsonEdges;

    setDeclarations(declarationsData);
    setTypeDeclarations(typeDeclarations);
    setNodes(nodeData);
    setEdges(jsonEdges);
    setInductionNodes(jsonInduction);
  }, [makeThisNode]);

  const verifyProofGlobal = async () => {
    /* check all nodes have correct syntax */
    setStopGlobalCheck(undefined);
    for await (const node of nodes) {
      // check might not be necessary with the onBlur, but better make sure
      node.data.thisNode.checkSyntax();
    }
    for (const node of nodes) {
      if (node.data.parsed !== true) {
        return;
      }
    }
    let correctEdges = true;
    for await (const node of nodes) {
      if (node.type !== "givenNode") {
        const output = await node.data.thisNode.checkEdges();
        correctEdges = correctEdges && output;
      }
    }
    for await (const node of nodes) {
      await node.data.thisNode.checkInternalAssertions();
    }
    setStopGlobalCheck(stop => {
      return !(stop === undefined && correctEdges);
    })
  }

  return (
    <div style={{ position: 'relative' }}>

      {/* START : Modals */}
      {/* START : Import Modal */}
      <Modal isOpen={importModalShow}
        onClose={() => { setImportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalImport />
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
        <ModalImport />
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
          <ModalHeader>Export Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalExport data={
              JSON.stringify({
                nodes: nodes,
                declarations: declarations.map(decl => decl.value),
                types: typeDeclarations.map(type => type.value),
                edges: edges,
                inductionNodes: inductionNodes,
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


      {/* START : Incorrect proof alert */}
      <div className="alert-container">
        {stopGlobalCheck === true && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof is not valid.
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
      {/* END : Incorrect Proof */}

      <div className="alert-container">
        {error && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            {error.column ?
              `Parsing for the last node failed. Error begins at column ${error.column}, from "${error.statement.value}"` :
              "Parsing for the last node failed. Check your syntax!"
            }
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

      <div className="alert-container">
        {error === null &&
          <Alert status='success' className="alert">
            <AlertIcon />
            <AlertTitle>Success!</AlertTitle>
            <AlertDescription>
              Parsing for current node was successful!
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
      {/* END : Export alert */}

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
                        <Tr key={index}>
                          <Td>{p.value}</Td>
                          <Td>{p.symbol}</Td>
                        </Tr>
                      )}
                    </Tbody>
                  </Table>
                </TableContainer>
              </PopoverBody>
            </PopoverContent>
          </Popover>
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
            nodes={(nodes as Node[]).concat(inductionNodes as Node[])}
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
