import './App.css';
import Flow from './Flow';

const rfStyle = {
  backgroundColor: '#D0C0F7',
};

const App = () => {
  return (
    <div className = "graph_header_container">
      <div className='header'>
        iProve
      </div>
      <div className='graph'>
        <Flow />
      </div>
    </div>
  );
}

export default App;