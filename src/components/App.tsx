import './App.css';
import Z3Solver from '../solver/Solver';
import { useEffect, useState } from 'react';
import Flow from './Flow';
import { ChakraProvider, Spinner } from '@chakra-ui/react'

const App = () => {
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    Z3Solver.initZ3().then(() => setLoading(false));

    return () => { };
  }, [])

  return (
    <ChakraProvider>
      <div className="graph_header_container">
        {loading === false ? (
          <div style={{ backgroundColor: '#B8CEFF' }}>
            <div className='header'>
              iProve
            </div>
            <div className='graph'>
              <Flow />
            </div>
            <Z3Solver.useZ3Button />
          </div>)
          : (
            <div className="loading">
              <Spinner
                thickness='4px'
                speed='0.65s'
                emptyColor='gray.200'
                color='#B8CEFF'
                size='xl'
              />
            </div>)

        }
      </div>
    </ChakraProvider>
  );
}

export default App;