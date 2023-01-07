import { init, Z3LowLevel, Z3_config } from 'z3-solver';


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
            const cfg: Z3_config = Z3EvalLib.mk_config();
            Z3EvalLib.set_param_value(cfg, "proof", "true")
            Z3EvalLib.set_param_value(cfg, "timeout", "150")
            const result = await Z3EvalLib.eval_smtlib2_string(
                Z3EvalLib.mk_context(cfg),
                "(declare-datatypes (T) ((IProvePFResult (IProveMkResult (IProveWellDefined Bool) (IProveResult T)))))\n"
                + str + "\n(check-sat)"); 
            console.log(result) ;
            return result;
        }

    }
}

export default Z3Solver;
