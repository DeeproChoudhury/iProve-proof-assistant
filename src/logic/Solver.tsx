import type { Z3HighLevel, Z3LowLevel } from 'z3-solver';

declare global {
    interface Window { z3Promise: Promise<Z3HighLevel & Z3LowLevel> } // use any to escape typechecking
}

const headers = [
   "(declare-datatypes (T) ((FunctionStatus (Success (get T)) (Failure (recover T)))))",
   "(declare-datatypes (T) ( (Maybe (Just (get T)) Nothing) ))"
]

const commands = [
   "(check-sat)"
]

export namespace Z3Solver {
   export async function loadZ3() {
      // eslint-disable-next-line @typescript-eslint/no-var-requires
      const z3 = require('z3-solver');

      // init z3
      const z3p: Promise<Z3HighLevel & Z3LowLevel> = window.z3Promise || (() => {
         return window.z3Promise = z3.init();
      })();

      return z3p;
   }

export async function solve(input: string, timeout: number = 13500): Promise<string> {
      // init z3
      const z3p = loadZ3();

      const { Z3 } = await z3p;

      // done on every snippet
      const cfg = Z3.mk_config();
      const ctx = Z3.mk_context(cfg);
      Z3.del_config(cfg);

      const timeStart = (new Date()).getTime();

      Z3.global_param_set('timeout', String(timeout));

      let output = '';
      let error = '';

      try {
         output = await Z3.eval_smtlib2_string(ctx, 
            headers.join("\n") + `\n${input}\n` + commands.join("\n")) ?? '';
      } catch (e) {
         // error with running z3
         error = (e as Error).message ?? 'Error message is empty';
      } finally {
         Z3.del_context(ctx);
      }

      if ((/unknown/).test(output)) {
         const timeEnd = (new Date()).getTime();
         if (timeEnd - timeStart >= timeout) {
            output = output + '\nZ3 timeout\n'
         }
      }

      console.log(headers.join("\n") + `\n${input}\n` + commands.join("\n"))
      console.log(output)
      // we are guaranteed to have non-undefined output and error
      return output;
      //return JSON.stringify({ output: String(output), error: error });

   }
}

export default Z3Solver;