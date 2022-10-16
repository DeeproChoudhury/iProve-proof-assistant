import './App.css';
// import Flow from './Flow.js';
import solver from './Solver';
import { useEffect } from 'react';
import Flow from './Flow';

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