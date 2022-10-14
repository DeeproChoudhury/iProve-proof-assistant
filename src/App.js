import './App.css';
import Flow from './Flow.js';
import { useEffect } from 'react';

const App = () => {
  useEffect(() => {
    // componentDidMount() {}
    const externalScript = document.createElement("script");
    externalScript.async = true;
    externalScript.type = "html/javascript";
    externalScript.src = "./Solver.js";
    document.head.append(externalScript);

    console.log("HELP");
    return () => {
      externalScript.remove();
    };
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