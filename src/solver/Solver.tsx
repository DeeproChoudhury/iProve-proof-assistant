import { init, Z3LowLevel } from 'z3-solver';

export namespace Z3Solver {
    
    var Z3EvalLib! : Z3LowLevel["Z3"];

    export async function initZ3() {
        const {
            Z3 // Low-level C-like API
        } = await init();

        if (Z3EvalLib === undefined) {
            Z3EvalLib = Z3;
            console.log("Z3 INIT COMPLETE");
        }
                
    } 

    export class Z3Prover {
        constructor(context: string) { }

        public async solve(str : string) {
            console.log(str)
            const cfg = Z3EvalLib.mk_config();
            Z3EvalLib.set_param_value(cfg, "proof", "true")
            const result = await Z3EvalLib.eval_smtlib2_string(
                Z3EvalLib.mk_context(cfg),
                str + "\n(check-sat)"); 
            console.log(result) ;
            return result;
        }

    }
}

export default Z3Solver;
