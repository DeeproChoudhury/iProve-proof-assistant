import { Arith, BoolCreation, ContextCtor, FuncDeclCreation, init, IntCreation, Z3_context } from 'z3-solver';
import { Z3LowLevel } from 'z3-solver'; 
import { Z3LowLevelType } from './Z3LowLevelType';

export namespace Z3Solver {
    
    var Z3EvalLib! : Z3LowLevelType ;

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
    
            console.log(await Z3EvalLib.eval_smtlib2_string(
                Z3EvalLib.mk_context(cfg),
                str)) ;
            
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