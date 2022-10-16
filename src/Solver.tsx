import { ContextCtor, init, IntCreation } from 'z3-solver';

const solver = async () => {
    const {
        //Z3, // Low-level C-like API
        Context, // High-level Z3Py-like API
    } = await init();
    const { Solver, Int, And } = Context('main');

    const x = Int.const('x');

    const solver = new Solver();
    solver.add(And(x.ge(0), x.le(9)));
    console.log(await solver.check());
}

export default solver;

export namespace Z3Solver {
    
    var HighLevelContext : ContextCtor | undefined;
    var HighLevelSolver : any | undefined;
    var Z3Int : IntCreation<"main">
    var Z3And : any;

    export async function initZ3() {
        const {
            // Z3, // Low-level C-like API
            Context, // High-level Z3Py-like API
        } = await init();

        if (HighLevelContext === undefined) {
            HighLevelContext = Context;
        
            const { Solver, Int, And } = HighLevelContext('main');
            HighLevelSolver = Solver;
            Z3Int = Int;
            Z3And = And;
    
            const x = Int.const('x');
        
            const solver = new HighLevelSolver();
            solver.add(And(x.ge(0), x.le(9)));
            console.log(await solver.check());
        }
        
    } 

    export async function useZ3() {
        if (HighLevelContext !== undefined) {
            // const { Solver, Int, And } = HighLevelContext('main');
            const solver = new HighLevelSolver();

            const x = Z3Int.const('x');
            solver.add(Z3And(x.ge(10), x.le(9)));
            
            console.log(await solver.check());
            console.log("OK");
        }
    }

    export function useZ3Button() {
        return(
            <button onClick={useZ3}>
                Z3
            </button>
        )
    }
}