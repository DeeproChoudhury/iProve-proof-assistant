import ReactFlow, {
  Background, Controls,
} from 'reactflow';
import 'reactflow/dist/style.css';
import CheckedEdge from './edges/CheckedEdge';
import ImplicationEdge from './edges/ImplicationEdge';
import InvalidEdge from './edges/InvalidEdge';
import './Flow.css';
import ModalExport from './modals/ModalExport';
import ModalImport from './modals/ModalImport';
import GivenNode from './nodes/GivenNode';
import GoalNode from './nodes/GoalNode';
import InductionNode from './nodes/InductionNode';
import ProofNode from './nodes/ProofNode';
import './nodes/ProofNode.css';
import { useIProveStore } from '../store/store';
import Sidebar from './Sidebar';
import Header from './Header';
import Alerts from './Alerts';
import ModalAddReasons from './modals/ModalAddReasons';

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
  const flowActions = useIProveStore(store => store.actions.flow);

  return (
    <div style={{ position: 'relative' }}>

      <ModalExport />
      <ModalImport />
      <ModalAddReasons />

      <Header />

      <Alerts />

      <div className="flowContainer">
        <Sidebar />
        <div className="flowCanvas">
          <ReactFlow
            nodes={nodes}
            nodeTypes={nodeTypes}
            edges={edges}
            edgeTypes={edgeTypes}
            disableKeyboardA11y={true} // disable keyboard movemement
            {...flowActions}
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
