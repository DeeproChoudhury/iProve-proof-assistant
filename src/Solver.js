const start = async () => {
    console.log("hi");
    const { init } = require('z3-solver/build/node');
    const {
        Z3, // Low-level C-like API
        Context, // High-level Z3Py-like API
    } = await init();
    console.log("RIP");  
    const { Solver, Int, And } = new Context('main');

    const x = Int.const('x');

    const solver = new Solver();
    solver.add(And(x.ge(0), x.le(9)));
    console.log(await solver.check());

    return () => {}
}

start()

// export { start };
    // const {
    //     loading,
    //     error,
    //     data
    //   } = useWasm({
    //     url: '../node_modules/z3-solver/build/z3-built.wasm'
    //   });

    // if (loading) {
    //     console.log ("Loading...");
    //     return;
    // }
    
    // if (error) {
    //     console.log ("An error has occurred"); 
    //     return;
    // }
    
    // const { Context } = await init();
    // console.log("RIP");    
    // // console.log("RIP");    

    // // var { init } = require('z3-solver');
    // const { Context } = (await init()).getFullVersion();
    // console.log("RIP2");    

    // const { Solver, Int } = new Context;
    // console.log("RIP3");    

    // const { Solver, Int, And } = new Context('main');
    
    // const x = Int.const('x');
     
    // const solver = new Solver();
    // solver.add(And(x.ge(0), x.le(9)));


// export default OurSolver;