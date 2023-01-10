import './App.css';
import Z3Solver from '../logic/Solver';
import { useEffect, useState } from 'react';
import Flow from './Flow';
import { ChakraProvider, Spinner } from '@chakra-ui/react'



const App = () => {
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    Z3Solver.loadZ3().then(() => setLoading(false));
    return () => { };
  }, [])

  return (
    <ChakraProvider>
      <div className="graph_header_container">
        {loading ? (
            <div className="loading">
              <Spinner
                thickness='4px'
                speed='0.65s'
                emptyColor='gray.200'
                color='#B8CEFF'
                size='xl'
              />
            </div>)
          : (
            <div className="mainContainer">
              <div className='graph'>
                <Flow />
              </div>
            </div>)

        }
      </div>
    </ChakraProvider>
  );
}

export default App;