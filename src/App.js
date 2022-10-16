import './App.css';
import Flow from './Flow.js';
import solver from './Solver.js';
import { useEffect } from 'react';

const App = () => {
  useEffect(() => {
    solver();
    
    return () => {  };
  }, [])
  return (
    <div style={{backgroundColor: '#B8CEFF'}}>
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