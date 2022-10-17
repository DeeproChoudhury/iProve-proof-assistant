import { Arith, ContextCtor, init, IntCreation } from 'z3-solver';

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
    // var Z3Int : IntCreation<"m">
    // var Z3And : any;
    // var Z3Or : any;
    // var Z3Implies : any;

    export async function initZ3() {
        const {
            // Z3, // Low-level C-like API
            Context, // High-level Z3Py-like API
        } = await init();

        if (HighLevelContext === undefined) {
            HighLevelContext = Context;
            console.log("Z3 INIT COMPLETE")
        }
        
    } 

    export class Z3Prover {
        private Z3Int! : IntCreation<string>;
        private Z3And! : any;
        private Z3Or! : any;
        private Z3Implies! : any;
        private HighLevelSolver! : any;
        
        private solver! : any;
        private variables : Map<string, Arith<string>>;

        constructor(context: string) {
            if (HighLevelContext !== undefined)
            {
                const { Solver, Int, And, Or, Implies, Eq } = HighLevelContext(context);
                this.HighLevelSolver = Solver;
                this.Z3Int = Int;
                this.Z3And = And;
                this.Z3Or = Or
                this.Z3Implies = Implies;

                this.solver = new this.HighLevelSolver();
            
            // const x = Int.const('x');
            // const solver = new HighLevelSolver();
            // solver.add(And(x.ge(0), x.le(9)));
            // console.log(await solver.check());
            }

            this.variables = new Map();

        }

        public const(x : string) {
            this.variables.set(x, this.Z3Int.const(x));
        }

        public addAnd(x : string, y: string) {
            const x_ = this.variables.get(x);
            const y_ = this.variables.get(y);
            if (x_ !== undefined && y_ !== undefined)
                this.solver.add(this.Z3And(x_.ge(0), y_.le(10)));
        }

        public async solve() {
            // console.log("ok");
            var self = this
            self.const("x");
            // console.log("x ok");

            self.addAnd("x","x");
            // console.log("x and ok");
            
            console.log(await self.solver.check());
        }

    }

    export function prove() {
        const prover = new Z3Prover("main");
        prover.solve()
    }

    export function useZ3Button() {
        return(
            <button onClick={prove}>
                Z3
            </button>
        )
    }
}