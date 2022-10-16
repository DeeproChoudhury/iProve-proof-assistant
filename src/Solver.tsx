import { init } from 'z3-solver';

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