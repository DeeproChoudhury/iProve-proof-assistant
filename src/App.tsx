import './App.css';
import Flow from './Flow';

const App = () => {
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