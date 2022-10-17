import './App.css';
import Flow from './Flow';
import { ChakraProvider, Heading } from '@chakra-ui/react'

const App = () => {
  return (
    <ChakraProvider>
      <div className = "graph_header_container">
        <div className='header'>
          <Heading>iProve</Heading>
        </div>
        <div className='graph'>
          <Flow />
        </div>
      </div>
    </ChakraProvider>
  );
}

export default App;