import { init, Z3LowLevel } from 'z3-solver';

export namespace Z3Solver {
    
    var Z3EvalLib! : Z3LowLevel["Z3"];

    export async function initZ3() {
        const {
            Z3, // Low-level C-like API
            Context, // High-level Z3Py-like API
        } = await init();

        if (Z3EvalLib === undefined) {
            Z3EvalLib = Z3;
            console.log("Z3 INIT COMPLETE");
        }
                
    } 

    export class Z3Prover {
        constructor(context: string) { }

        public async solve(str : string) {
            const cfg = Z3EvalLib.mk_config();
            Z3EvalLib.set_param_value(cfg, "proof", "true")
            const result = await Z3EvalLib.eval_smtlib2_string(
                Z3EvalLib.mk_context(cfg),
                str); 
            console.log(result) ;
            return result;
        }

    }

    export function prove() {
        const Z3 = new Z3Prover("");
        Z3.solve("(declare-const x Int)\n(assert (not (= x x)))\n(check-sat)\n")
    }

    export function useZ3Button() {
        return(
            <button onClick={prove}>
                Z3
            </button>
        )
    }
}

export default Z3Solver;
