import './App.css';
// import Flow from './Flow.js';
import { Z3Solver } from './Solver';
import { useEffect } from 'react';
import Flow from './Flow';

const App = () => {
  useEffect(() => {
    Z3Solver.initZ3();
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
      <Z3Solver.useZ3Button />
    </div>
  );
}

export default App;