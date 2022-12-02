import { init, Z3LowLevel, Z3_config } from 'z3-solver';

const BUILTIN_LISTS = `
(declare-const IProveUnderspecifiedInt Int)

(define-fun-rec ListExchange ((ls (List Int)) (cs (List Int))) (List Int)
   (if ((_ is nil) ls)
      cs
      (ListExchange (tail ls) (insert (head ls) cs))
   )
)

(define-fun-rec ListReverse ((ls (List Int))) (List Int) (ListExchange ls nil))
(define-fun-rec ListConcat ((ls (List Int)) (cs (List Int))) (List Int) 
   (ListExchange (ListReverse ls) cs))

(define-fun-rec ListElem ((ls (List Int)) (i Int)) Int
   (if ((_ is nil) ls)
      IProveUnderspecifiedInt
      (if (= i 0)
         (head ls)
         (ListElem (tail ls) (- i 1))
      )
   )
)

(define-fun-rec ListSlice ((ls (List Int)) (s Int) (e Int) (cs (List Int))) (List Int)
   (if ((_ is nil) ls)
      (ListReverse cs)
      (if (= e 0)
         (ListReverse cs)
         (if (= s 0)
            (ListSlice (tail ls) 0 (- e 1) (insert (head ls) cs))
            (ListSlice (tail ls) (- s 1) (- e 1) cs)
         )
      )
   )
)

`;


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
                BUILTIN_LISTS + str + "\n(check-sat)"); 
            console.log(result) ;
            return result;
        }

    }
}

export default Z3Solver;
