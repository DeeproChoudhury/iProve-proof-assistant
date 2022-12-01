import { defineStyle } from "@chakra-ui/react";
import * as AST from "../types/AST";
import { FunctionData, PatternData, PatternElem } from "../types/LogicInterface";
import { conjunct, getSelector, isTerm } from "../util/trees";
import Z3Solver from "./Solver";
import { fnSMT } from "./util";

export type ProofOutcome = ProofError | ProofVerdict
type ProofVerdict = {
    kind: "Valid" | "False" | "Unknown",
    info?: string
}
type ProofError = {
    kind: "Error",
    emitter: "IProve" | "Z3",
    msg: string
}

export class LogicInterface {
    // persist after reset
    types: AST.TypeDef[] = [];
    rendered_types: string[] = [];
    declarations: AST.Line[] = [];
    function_declarations: Map<string, AST.FunctionDeclaration> = new Map();
    rendered_tuples: Map<number, string> = new Map();
    global_fn_defs: Map<string, AST.FunctionDefinition[]> = new Map();

    // change on reset
    givens: AST.Line[] = [];
    goal: AST.Term | undefined;
    rendered_givens: string[] = [];
    rendered_goal: string | undefined;
    local_fn_defs: Map<string, AST.FunctionDefinition[]> = new Map();
    error_state: string | undefined;

    error(state: string) { this.error_state = state; }
    resolve_error() 
        { let e = this.error_state; this.error_state = undefined; return e; }
    
    reset_tuples() { this.rendered_tuples = new Map; }

    async context_free_entails(
        declarations: AST.Line[], types: AST.TypeDef[], reasons: AST.Line[], goal: AST.Term)
        : Promise<ProofOutcome> {
            this.setTypes(types)
            this.setDeclarations(declarations)
            return this.entails(reasons, goal)
        }

    async entails(reasons: AST.Line[], goal: AST.Line, reset: boolean = true): Promise<ProofOutcome> {
        if (reset) this.newProof()

        let E: string | undefined
        for (let r of reasons) {
            this.pushGiven(r)
            E = this.resolve_error();
            if (E) return { kind: "Error", emitter: "IProve", msg: E }
        }

        this.setGoal(goal)
        E = this.resolve_error();
        if (E) return { kind: "Error", emitter: "IProve", msg: E }
        const rendered = `${LI}`;
        E = this.resolve_error();
        if (E) return { kind: "Error", emitter: "IProve", msg: E }

        const localZ3Solver = new Z3Solver.Z3Prover("");
        const response = await localZ3Solver.solve(rendered);

        if (response.startsWith("unsat")) {
            return { kind: "Valid" }
        } else if (response.startsWith("sat")) {
            return { kind: "False" }
        } else if (response.startsWith("unknown")) {
            return { kind: "Unknown" }
        } else {
            return {
                kind: "Error",
                emitter: "Z3",
                msg: response
            }
        }
    }

    // Call this method before setting givens and goal for the current
    // proof
    newProof(): void {
        this.goal = undefined;
        this.givens = [];

        this.rendered_goal = undefined;
        this.rendered_givens = [];

        this.local_fn_defs = new Map();
    }

    setTypes(A: AST.TypeDef[]): void {
        this.types = A;
        this.rendered_types = A.map(renderNode)
    }

    pushFnDef(A: AST.FunctionDefinition, M: Map<string, AST.FunctionDefinition[]>) {
        let defs = M.get(A.ident)
        if (!defs) M.set(A.ident, [A])
        else defs.push(A)
    }

    setDeclarations(A: AST.Line[]): void {
        this.declarations = A;
        this.function_declarations = new Map;
        this.global_fn_defs = new Map;

        A.forEach((t) => {
            if (t.kind == "FunctionDeclaration") {
                if (!this.function_declarations.has(t.symbol))
                    this.function_declarations.set(t.symbol, t)
                else
                    this.error(`Cannot redeclare function: ${t.symbol}`)
            } else if (t.kind == "FunctionDefinition")
                this.pushFnDef(t, this.global_fn_defs)
        })
    }

    // Add instance given
    pushGiven(n: AST.Line): boolean {
        switch(n.kind) {
            case "FunctionDeclaration":
                this.error("Cannot declare functions outside of Declarations")
                return false
            case "FunctionDefinition":
                this.error("Cannot define functions outside of Declarations")
                return false
            case "TypeDef":
                this.error("Cannot declare types outside of Declarations")
                return false

            case "BeginScope":
            case "EndScope":
            case "Assumption":
            case "Skolemize":
                return !this.error_state;
        }

        this.givens.push(n)
        return !this.error_state;
    }
    popGiven() { this.givens.pop() }

    // Set the instance goal. Returns the previous one. Note that if we were
    // to stack goals P, Q, by De Morgan this is exactly setting the goal to
    // P || Q, so we force this instead to increase usability.
    //
    // For now, we do not allow function definitions as goals. This would
    // be useful sugar in proving the equivalence of function definitions
    // but also a bit trickier and not encountered in 1/2 year.
    setGoal(n: AST.Line): AST.Term | undefined {
        if (!isTerm(n)) {
            this.error(`Only terms can be set as goals (not ${n.kind})`)
            return
        }

        const old = this.goal; this.goal = n;
        return old
    }

    createTuple(n: number): boolean {
        if (this.rendered_tuples.has(n)) return false;

        let thisID = `IProveTuple${n}`
        let elems: string[] = [];
        let params: string[] = [];
        for (let i = 1; i <= n; i++) {
            params.push(`PT${i}`)
            elems.push(`(${getSelector(i - 1)} PT${i})`)
        }

        this.rendered_tuples.set(n,
            `(declare-datatypes (${params.join(" ")}) ((${thisID} (mk-tuple ${elems.join(" ")}))))`
        )
        console.log("RTUP", this.rendered_tuples)
        return true;
    }

    renderFunctionDeclaration(ident: string, consts: string[]): [string, string | undefined][] | undefined {
        SID.n = 0
        let A = this.global_fn_defs.get(ident);
        let defs: AST.FunctionDefinition[] 
            = (A ?? []).concat(this.local_fn_defs.get(ident) ?? []);
        let decl = this.function_declarations.get(ident)

        if (!decl) {
            this.error(`Function ${ident} must be declared before it is defined`)
            return;
        } 
        if (!defs.length) return [[`${decl.symbol} ${renderNode(decl.type)}`, undefined]];

        let params: string[] = []
        let nparams = decl.type.argTypes.length;

        for (let i = 0; i < nparams; i++) params.push(`IProveParameter${i}`)

        let pdatas: [PatternData, AST.Term][] = [];
        for (let a of defs) {
            if (a.params.length != nparams) {
                this.error(`Function definition for ${a.ident} has an incorrect number of parameters. Expecting ${nparams}, found ${a.params.length}`)
                return
            }

            let idx: number = 0;
            let concu: PatternData = [];
            for (let [i,p] of a.params.entries()) {
                concu = concu.concat(renderPattern(p, `IProveParameter${SID.n++}`))
                pdatas.push([concu, (a.def as AST.Term)]);
            }
        }

        let sections: string[] = [];
        console.log("PDATAS", pdatas)
        for (let [i, [p, d]] of pdatas.entries()) {
            let sec: string = renderNode(d);
            const alt: string = `(${ident}__${i + 1} ${params.join(" ")})`
            for (let D of p.reverse()) {
                console.log("HERE D", D)
                if (D.kind == "Condition")
                    sec = `(if ${D.value} ${sec} ${alt})`
                else
                    sec = `(let (${D.value}) ${sec})`
            }

            sections.push(sec)
        }

        consts.push(`IProveConstant${consts.length} ${renderNode(decl.type.retType)}`)
        sections.push(`IProveConstant${consts.length - 1}`);

        let rendered_params: string[] = [];
        for (let i = 0; i < nparams; i++)
            rendered_params.push(`(${params[i]} ${renderNode(decl.type.argTypes[0])})`)
        
        let type = `(${rendered_params.join(" ")}) ${renderNode(decl.type.retType)}`


        let R: [string, string][] = []
        for (let [i, s] of sections.entries()) {
            console.log("A SECTION", i, s)
            R.push([
                `${ident}${(i > 0) ? `__${i}` : ""} ${type}`,
                s
            ])
        }
        return R
    }

    toString(): string {
        let res = "";
        let types = "";

        // TYPES
        for (let v of this.rendered_types)
            types += `${v}\n`

        // FUNCTIONS
        let decls: string[] = []
        let defns: string[] = []
        let consts: string[] = []
        for (let [k, _] of this.function_declarations) {
            let rendered = this.renderFunctionDeclaration(k, consts);
            if (this.error_state || !rendered)
                return `ERROR: ${this.error_state}`
            for (let rr of rendered) {
                if (!rr[1])
                    res += `(declare-fun ${rr[0]})\n`
                else {
                    decls.push(rr[0]); defns.push(rr[1]);
                }
            }
        }

        res += consts.map(x => `(declare-const ${x})`)
        let tDecl = decls.map(x => `(${x})`).join(" ")
        let tDefn = defns.map(x => `${x}`).join(" ")
        console.log("BIG WAN")
        console.log(tDecl)
        console.log(tDefn)
        res += `\n\n(define-funs-rec\n    (${tDecl}) \n    (${tDefn})\n)\n\n`

        console.log(res)

        // GLOBALS
        for (let v of this.declarations) {
            switch (v.kind) {
                case "FunctionDefinition":
                case "FunctionDeclaration":
                    break;
                case "VariableDeclaration":
                    res += `${renderNode(v)}\n`; break;
                case "TypeDef":
                    types += `${renderNode(v)}\n`; break;

                default:
                    res += `(assert ${renderNode(v)})`
            }
        }

        // GIVENS
        for (let v of this.givens) {
            switch (v.kind) {
                case "VariableDeclaration":
                    res += renderNode(v); break;
                default:
                    res += `(assert ${renderNode(v)})`
            }
            res += "\n"
        }

        // GOAL
        res += `(assert (not ${renderNode(this.goal)}))\n`

        //console.log("PRETUPE", res)
        // TUPLES
        for (let [_,v] of this.rendered_tuples)
            res = `${v}\n` + res

        return types + res;
    }
}

let SID: {n : number} = { n : 0 }
const mk_bind = (s: string): PatternElem => ({ kind: "Binding", value: s })
const mk_cond = (s: string): PatternElem => ({ kind: "Condition", value: s })
function renderPattern(a: AST.Pattern, name: string): PatternData {
    switch(a.kind) {
        case "SimpleParam":
            return [mk_bind(`(${a.ident} ${name})`)]
        case "EmptyList":
            return [mk_cond(`(is-nil ${name})`)] 
        case "ConsParam": {
            let aID = `IProveParameter${SID.n++}`
            let bID = `IProveParameter${SID.n++}`
            let R = [
                mk_cond(`(not (is-nil ${name}))`),
                mk_bind(`(${aID} (head ${name}))`),
                mk_bind(`(${bID} (tail ${name}))`)
            ]
            R = R.concat(renderPattern(a.A, aID))
                 .concat(renderPattern(a.B, bID))

            return R
        }
        case "ConstructedType": {
            let R: PatternData = []
            R.push(mk_cond(`(is-${a.c} ${name})`))

            for (let [i,v] of a.params.entries()) {
                let npid = `IProveParameter${SID.n++}`;
                let NPD = renderPattern(v, npid)
                R.push(mk_bind(`(${npid} (${getSelector(i)} ${name}))`))
                R = R.concat(NPD)
            }
            return R
        }
        case "TuplePattern": {
            let R: PatternData = []
            R.push(mk_cond(`(is-mk-tuple ${name})`))

            for (let [i,v] of a.params.entries()) {
                let npid = `IProveParameter${SID.n++}`;
                let NPD = renderPattern(v, npid)
                R.push(mk_bind(`(${npid} (${getSelector(i)} ${name}))`))
                R = R.concat(NPD)
            }
            return R
        }
    }
}

function renderNode(a: AST.ASTNode | undefined): string {
    if (!a) return "NULL";

    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(renderNode).join(" ")})  ${renderNode(a.retType)}`;
        case "VariableBinding": return `(${renderNode(a.symbol)} ${a.type ? renderNode(a.type) : "Int"})`;
        case "FunctionDeclaration": return "";
        case "VariableDeclaration": return `(declare-const ${renderNode(a.symbol)} ${a.type ? `${renderNode(a.type)}` : "Int"})`;
        case "Variable": return a.ident;
        case "FunctionApplication": {
            switch (a.fn) {
                case "List":
                case "Array":
                    return renderNode({
                        kind: "ArrayLiteral",
                        elems: a.params
                    })
                case "Tuple":
                    LI.createTuple(a.params.length)
                    return `(mk-tuple ${a.params.map(renderNode).join(" ")})`
                default:
                    return (a.params.length)
                    ? `(${fnSMT(a.fn)} ${a.params.map(renderNode).join(" ")})`
                    : fnSMT(a.fn)
            }
        }
        case "QuantifierApplication": return `(${a.quantifier === "E" ? "exists" : "forall"} (${a.vars.map(renderNode).join(" ")}) ${renderNode(a.term)})`;
        case "EquationTerm": return `${renderNode(a.lhs)} ::= ${renderNode(a.rhs)}`;
        case "ParenTerm": return renderNode(a.term);
    
        case "TypeDef": {
            let cons = a.cases.map(renderNode).join(" ");
            let type_params = a.params.join(" ");
            return `(declare-datatypes (${type_params}) ((${a.ident} ${cons})))`
        }
        case "TypeConstructor": {
            let params = a.params.map(
                (e, i) => (`(${a.selectors[i]} ${renderNode(e)})`));
            return (params.length)
                ? `(${a.ident} ${params.join(" ")})`
                : a.ident
        }

        case "ParamType":
            return `(${a.ident} ${a.params.map(renderNode).join(" ")})`
        case "ListType":
            return `(List ${renderNode(a.param)})`
        case "TupleType": {
            let N = a.params.length;
            LI.createTuple(N);
            return `(IProveTuple${N} ${a.params.map(renderNode).join(" ")})`;
        }
        
        case "ArrayLiteral": {
            let R = "nil";
            for (let e of a.elems)
                R = `(insert ${renderNode(e)} ${R})`
            return R
        }

        case "BeginScope":
        case "EndScope":
        case "Assumption":
        case "Skolemize":
            return "";
        
        // THESE CASES SHOULD NEVER BE ENCOUNTERED \/
        case "FunctionDefinition":
        case "Guard":
        case "SimpleParam":
        case "ConsParam":
        case "EmptyList":
        case "ConstructedType":
        case "TuplePattern":
            return "NULL";
        // THESE CASES SHOULD NEVER BE ENCOUNTERED ^^
    }
}

export const LI = new LogicInterface();
