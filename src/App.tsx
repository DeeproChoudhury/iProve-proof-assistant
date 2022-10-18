import './App.css';
// import Flow from './Flow.js';
import Z3Solver from './Solver';
import { useEffect, useState } from 'react';
import Flow from './Flow';
import { ChakraProvider, Heading } from '@chakra-ui/react'

const App = () => {
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    Z3Solver.initZ3().then(() => setLoading(false));

    return () => {  };
  }, [])
  
  return (
    <ChakraProvider>
      <div className = "graph_header_container">
      {loading === false ? (
        <div style={{backgroundColor: '#B8CEFF'}}>
          <div className='header'>
            iProve
          </div>
          <div className='graph'>
            <Flow />
          </div>
          <Z3Solver.useZ3Button />
        </div>) 
        : (
        <div className='header'>
          <h1>LOADING :-)</h1>
        </div>)
        
        }
      </div>
    </ChakraProvider>
  );
}

export default App;