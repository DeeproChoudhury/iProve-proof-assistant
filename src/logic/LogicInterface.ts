import { defineStyle } from "@chakra-ui/react";
import { ThemeProvider } from "@emotion/react";
import { StringChain } from "lodash";
import { type } from "os";
import * as AST from "../types/AST";
import { FunctionData, PatternData, PatternElem } from "../types/LogicInterface";
import { conjunct, getSelector, imply, isDeclaration, isTerm, mk_var, PrimitiveType, underdetermine } from "../util/trees";
import Z3Solver from "./Solver";
import { gen_decls } from "./unifier";
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

export const IPROVE_LIST: AST.TypeDef = {
    kind: "TypeDef",
    ident: "IProveList",
    params: ["T"],
    cases: [
        { kind: "TypeConstructor", params: [], ident: "nil", selectors: [] },
        { kind: "TypeConstructor", params: [PrimitiveType("T"), {
            kind: "ParamType",
            ident: "IProveList",
            params: [PrimitiveType("T")]
        }], ident: "IProveInsert", selectors: ["head", "tail"] }
    ]
}

const ListSlice = (t: string) => `
(define-fun-rec ListSlice ((ls (IProveList ${t})) (s Int) (e Int) (cs (IProveList ${t}))) (IProveList ${t})
   (if ((_ is nil) ls)
      (ListReverse cs)
      (if (= e 0)
         (ListReverse cs)
         (if (= s 0)
            (ListSlice (tail ls) 0 (- e 1) (IProveInsert (head ls) cs))
            (ListSlice (tail ls) (- s 1) (- e 1) cs)
         )
      )
   )
)`;

const ListElem = (t: string) => `
(define-fun-rec ListElem ((ls (IProveList ${t})) (i Int)) ${t}
   (if ((_ is nil) ls)
      IProveUnderspecified${t}
      (if (= i 0)
         (head ls)
         (ListElem (tail ls) (- i 1))
      )
   )
)`;

const ListReverse = (t: string) => `
(define-fun-rec ListReverse ((ls (IProveList ${t}))) (IProveList ${t}) (ListExchange ls (as nil (IProveList ${t}))))`;

const ListConcat = (t: string) => `
(define-fun-rec ListConcat ((ls (IProveList ${t})) (cs (IProveList ${t}))) (IProveList ${t}) 
   (ListExchange (ListReverse ls) cs))`;

const ListExchange = (t: string) => `
(define-fun-rec ListExchange ((ls (IProveList ${t})) (cs (IProveList ${t}))) (IProveList ${t})
   (if ((_ is nil) ls)
      cs
      (ListExchange (tail ls) (IProveInsert (head ls) cs))
   )
)`;

const ListUnderspecified = (safe: string, unsafe: string) =>
    `(declare-const IProveUnderspecified${safe} ${unsafe})`;

export type ListOp = "Slice" | "Underspecified" | "Exchange" | "Reverse" | "Concat" | "Elem"
export function renderListOperation(op: ListOp, type: AST.Type): string {
    if (type.kind != "ListType" && !(type.kind == "ParamType" && type.ident == "List")) return "";
    let tp = (type.kind == "ListType") ? type.param : type.params[0]
    let ty = renderNode(tp)
    switch (op) {
        case "Concat":
            return ListConcat(ty)
        case "Elem":
            return ListElem(ty)
        case "Exchange":
            return ListExchange(ty)
        case "Reverse":
            return ListReverse(ty)
        case "Slice":
            return ListSlice(ty)
        case "Underspecified":
            return ListUnderspecified(LI.displaySafeType(tp), ty)
    }
}


export class LogicInterface {
    // persist after reset
    types: AST.TypeDef[] = [IPROVE_LIST];
    rendered_types: string[] = [];
    declarations: AST.Line[] = [];
    function_declarations: Map<string, AST.FunctionDeclaration> = new Map();
    rendered_tuples: Map<number, string> = new Map();
    global_fn_defs: Map<string, AST.FunctionDefinition[]> = new Map();
    partial_funs: Set<string> = new Set();
    partial_undets: Set<string> = new Set();
    defined_types: Map<string, AST.TypeDef> = new Map();

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

    async entails(reasons: AST.Line[], goal: AST.Line, strip_types: boolean = false, reset: boolean = true): Promise<ProofOutcome> {
        if (reset) this.newProof()

        let E: string | undefined
        for (let r of reasons) {
            console.log(r);
            this.pushGiven(r)
            E = this.resolve_error();
            if (E) return { kind: "Error", emitter: "IProve", msg: E }
        }

        this.setGoal(conjunct([goal, LI.wellDef(goal as AST.Term)]) as AST.Term)
        E = this.resolve_error();
        if (E) return { kind: "Error", emitter: "IProve", msg: E }
        const rendered = this.toString(strip_types);
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
        this.types = [IPROVE_LIST].concat(A);
        for (let T of A)
            this.defined_types.set(T.ident, T)
        this.rendered_types = A.map(renderNode)
    }

    pushFnDef(A: AST.FunctionDefinition, M: Map<string, AST.FunctionDefinition[]>) {
        let defs = M.get(A.ident)
        if (!defs) M.set(A.ident, [A])
        else defs.push(A)

        this.partial_funs.add(A.ident);
    }

    setDeclarations(A: AST.Line[]): void {
        this.declarations = A;
        this.function_declarations = new Map;
        this.global_fn_defs = new Map;
        this.partial_funs = new Set;

        A.forEach((t) => {
            if (t.kind == "FunctionDeclaration") {
                if (!this.function_declarations.has(t.symbol))
                    this.function_declarations.set(t.symbol, t)
                else
                    this.error(`Cannot redeclare function: ${t.symbol}`)
            } else if (t.kind == "FunctionDefinition")
                this.pushFnDef(t, this.global_fn_defs)
            else if (t.kind == "TypeDef")
            this.defined_types.set(t.ident, t)
        })
    }

    displaySafeType(T: AST.Type): string {
        switch(T.kind) {
            case "ListType":
                return `IProveList_${this.displaySafeType(T.param)}`;
            case "ParamType":
                let ti = T.ident == "List" ? "IProveList" : T.ident
                return `${T.ident}_${T.params.map(this.displaySafeType).join("_")}`;
            case "PrimitiveType":
                return T.ident
            case "TupleType":
                return `__${T.params.map(this.displaySafeType).join("_")}__`;
        }
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

    renderTermOrGuard(G: AST.Guard | AST.Term, alt: string): string {
        if (!(G.kind == "Guard")) return `(IProveMkResult ${renderNode(LI.wellDef(G))} ${renderNode(G)})`
        return this.renderGuard(G, alt)
    }

    renderGuard(G: AST.Guard, alt: string): string {
        let t_alt: string = alt;
        if (G.next)
            t_alt = this.renderGuard(G.next, alt)
        return `(if ${renderNode(G.cond)} (IProveMkResult ${renderNode(LI.wellDef(G.res))} ${renderNode(G.res)}) ${t_alt})`;
    }

    wellDef(T: AST.Term): AST.Term {
        switch(T.kind) {
            case "ArrayLiteral":
                return conjunct(T.elems.map(LI.wellDef)) as AST.Term;
            case "EquationTerm":
                return imply(LI.wellDef(T.rhs), LI.wellDef(T.lhs));
            case "FunctionApplication":
                let is_partial = LI.partial_funs.has(T.fn)
                let definedPredicate: AST.PrefixApplication = {
                    kind: "FunctionApplication",
                    appType: "PrefixFunc",
                    params: T.params,
                    fn: `IProveWellDefined_${T.fn}`
                }
                let R = conjunct(T.params.map(LI.wellDef)) as AST.Term;
                return is_partial ? conjunct([R, definedPredicate]) as AST.Term : R;
            case "ParenTerm":
                return LI.wellDef(T.term);
            case "QuantifierApplication":
                return {
                    kind: "QuantifierApplication",
                    quantifier: T.quantifier,
                    vars: T.vars,
                    var_nesting: T.var_nesting,
                    term: LI.wellDef(T.term)
                }
            case "Variable":
                return mk_var("true");
        }
    }

    
    

    renderFunctionDeclaration(ident: string, consts: Set<string>): [string, string | undefined][] | undefined {
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
        
        SID.n = 0
        for (let i = 0; i < nparams; i++) params.push(`IProveParameter${SID.n++}`)

        let pdatas: [PatternData, AST.Term | AST.Guard][] = [];
        for (let a of defs) {
            if (a.params.length != nparams) {
                this.error(`Function definition for ${a.ident} has an incorrect number of parameters. Expecting ${nparams}, found ${a.params.length}`)
                return
            }

            let idx: number = 0;
            let concu: PatternData = [];
            for (let [i,p] of a.params.entries()) {
                concu = concu.concat(renderPattern(p, `IProveParameter${i}`, decl.type.argTypes[i]))
            }
            pdatas.push([concu, a.def]);
        }

        let sections: string[] = [];
        console.log("PDATAS", pdatas)
        const overall_alt = `(IProveMkResult false IProveUnderdetermined${this.displaySafeType(decl.type.retType)})`
        for (let [i, [p, d]] of pdatas.entries()) {
            const alt: string = `(${ident}__${i + 1} ${params.join(" ")})`;
            let sec: string = this.renderTermOrGuard(d, alt);
            for (let D of p.reverse()) {
                console.log("HERE D")
                if (D.kind == "Condition")
                    sec = `(if ${D.value} ${sec} ${alt})`
                else
                    sec = `(let (${D.value}) ${sec})`
            }

            sections.push(sec)
        }
        
        sections.push(overall_alt);

        let rendered_params: string[] = [];
        for (let i = 0; i < nparams; i++)
            rendered_params.push(`(${params[i]} ${renderNode(decl.type.argTypes[0])})`)
        
        let type = `(${rendered_params.join(" ")}) ${renderNode(decl.type.retType)}`

        const rt: string = renderNode(decl.type.retType);
        consts.add(`(declare-const IProveUnderdetermined${this.displaySafeType(decl.type.retType)} ${rt})`)

        let R: [string, string][] = []
        R.push([`${ident} ${type}`, `(IProveResult (${ident}__0 ${params.join(" ")}))`])
        R.push([
            `IProveWellDefined_${ident} (${rendered_params.join(" ")}) Bool`,
            `(IProveWellDefined (${ident}__0 ${params.join(" ")}))`])
        for (let [i, s] of sections.entries()) {
            console.log("A SECTION", i, s)
            R.push([
                `${ident}__${i} (${rendered_params.join(" ")}) (IProvePFResult ${renderNode(decl.type.retType)})`,
                s
            ])
        }
        return R
    }

    renderDatatypes(strip_types: boolean = false): string {
        let arities = this.types.map((x) => `(${x.ident} ${x.params.length})`)
        let decls = (strip_types ? this.types.map(underdetermine) : this.types)
            .map((x) => `(par (${x.params.join(" ")}) (${x.cases.map(renderNode).join(" ")}))`)
        return`(declare-datatypes (${arities.join(" ")}) (${decls.join(" ")}))`
    }

    MathOperators = new Set(["+", "-", "/", "*", "%"])
    BooleanOperators = new Set(["||", "&", "~", "->", "<->", "in", "=", "=="])
    ListOperators = new Set(["ArraySelect", "ArraySlice", "++"])
    deriveType(T: AST.Term, V: Map<string, AST.Type | undefined>, F: Map<string, AST.FunctionType>): AST.Type | undefined {
        if (!T) return undefined;
        switch(T.kind) {
            case "ArrayLiteral":
                let A = (T.elems.length > 0) ? this.deriveType(T.elems[0], V, F) : undefined
                return A ? {
                    kind: "ListType",
                    param: A
                 } : undefined
            case "FunctionApplication":
                if (this.MathOperators.has(T.fn) || this.ListOperators.has(T.fn))
                    return this.deriveType(T.params[0], V, F)
                else if (this.BooleanOperators.has(T.fn))
                    return PrimitiveType("Bool")
                else if (T.fn == ":") {
                    if (!T.params[1]) return undefined;
                    return this.deriveType(T.params[1], V, F)
                }
                return F.get(T.fn)?.retType
            case "ParenTerm":
                return this.deriveType(T.term, V, F)
            case "Variable":
                if (/^-?\d+$/.test(T.ident)) return PrimitiveType("Int");
                if (T.ident == "true" || T.ident == "false") return PrimitiveType("Bool");
                return V.get(T.ident)
            case "QuantifierApplication":
            case "EquationTerm":
                return PrimitiveType("Bool")
        }
    }

    extractListOps(T: AST.Term | undefined, R: [ListOp, AST.Type | undefined][], V: Map<string, AST.Type | undefined>, F: Map<string, AST.FunctionType>): void  {
        if (!T) return;

        switch(T.kind) {
            case "ArrayLiteral":
                for (let e of T.elems) this.extractListOps(e, R, V, F)
                break;
            case "FunctionApplication":
                for (let e of T.params) this.extractListOps(e, R, V, F)
                let derived = this.deriveType(T.params[0], V, F);
                switch(T.appType) {
                    case "ArrayElem":
                        R.push(["Underspecified", derived]);
                        R.push(["Elem", derived]);
                        break;
                    case "ArraySlice":
                        R.push(["Exchange", derived]);
                        R.push(["Reverse", derived]);
                        R.push(["Slice", derived]);
                        break;
                    case "InfixOp":
                    case "InfixFunc":
                        if (T.fn == "++") {
                            R.push(["Exchange", derived]);
                            R.push(["Reverse", derived]);
                            R.push(["Concat", derived]);
                        }
                        break;
                }
                break;
            case "ParenTerm":
                this.extractListOps(T.term, R, V, F)
                break;
            case "Variable":
                break;
            case "QuantifierApplication":
                let old: [string, AST.Type | undefined][] = []
                for (let vb of T.vars) {
                    old.push([vb.symbol.ident, V.get(vb.symbol.ident)])
                    V.set(vb.symbol.ident, vb.type)
                }
                this.extractListOps(T.term, R, V, F)
                for (let [s,v] of old) V.set(s, v)
                break;
            case "EquationTerm":
                this.extractListOps(T.lhs, R, V, F)
                this.extractListOps(T.rhs, R, V, F)
        }
    }

    updateWithDeclaration(D: AST.Line, V: Map<string, AST.Type | undefined>, F: Map<string, AST.FunctionType>): void {
        switch (D.kind) {
            case "FunctionDeclaration":
                F.set(D.symbol, D.type)
                break;
            case "SortDeclaration":
                break;
            case "VariableDeclaration":
                V.set(D.symbol.ident, D.type)
        }
    }



    toString(strip_types: boolean = false): string {
        let res = "";
        let types = this.renderDatatypes(strip_types);

        let V: Map<string, AST.Type | undefined> = new Map;
        let F: Map<string, AST.FunctionType> = new Map;
        let list_ops: [ListOp, AST.Type | undefined][] = [];

        // FUNCTIONS
        let decls: string[] = []
        let defns: string[] = []
        let consts: Set<string> = new Set;

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

        res += Array.from(consts).join("\n");
        let tDecl = decls.map(x => `(${x})`).join(" ")
        let tDefn = defns.map(x => `${x}`).join(" ")
        res += `\n\n(define-funs-rec\n    (${tDecl}) \n    (${tDefn})\n)\n\n`

        console.log(res)

        // GLOBALS
        for (let v of this.declarations) {
            this.updateWithDeclaration(v, V, F)
            switch (v.kind) {
                case "FunctionDefinition":
                case "FunctionDeclaration":
                    break;
                case "VariableDeclaration":
                    res += `${renderNode(v)}\n`; break;
                case "TypeDef":
                    types += `${renderNode(v)}\n`; break;
                default:
                    if (isTerm(v)) this.extractListOps(v, list_ops, V, F);
                    res += `(assert ${renderNode(v)})`
            }
        }

        // GIVENS
        for (let v of this.givens) {
            this.updateWithDeclaration(v, V, F)
            switch (v.kind) {
                case "VariableDeclaration":
                    res += renderNode(v); break;
                default:
                    if (isTerm(v)) this.extractListOps(v, list_ops, V, F);
                    res += `(assert ${renderNode(v)})`
            }
            res += "\n"
        }

        // GOAL
        this.extractListOps(this.goal, list_ops, V, F);
        res += `(assert (not ${renderNode(this.goal)}))\n`

        // TUPLES
        for (let [_,v] of this.rendered_tuples)
            res = `${v}\n` + res

        // LISTS
        let LIST_OPS: Set<string> = new Set
        for (let [o, t] of list_ops) {
            if (!t) continue;
            LIST_OPS.add(renderListOperation(o, t))
        }

        return types + Array.from(LIST_OPS).join("\n") + res;
    }
}

let SID: {n : number} = { n : 0 }
const mk_bind = (s: string): PatternElem => ({ kind: "Binding", value: s })
const mk_cond = (s: string): PatternElem => ({ kind: "Condition", value: s })
export function renderPattern(a: AST.Pattern, name: string, t: AST.Type): PatternData {
    switch(a.kind) {
        case "SimpleParam":
            if (t.kind == "PrimitiveType") {
                let tdef = LI.defined_types.get(t.ident)
                if (!tdef) return [mk_bind(`(${a.ident} ${name})`)]
                for (let C of tdef.cases) {
                    if (C.params.length == 0 && C.ident == a.ident)
                     return [mk_cond(`(is-${a.ident} ${name})`)]
                }
            } 
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
            R = R.concat(renderPattern(a.A, aID, t))
                 .concat(renderPattern(a.B, bID, t))

            return R
        }
        case "ConstructedType": {
            let R: PatternData = []
            R.push(mk_cond(`(is-${a.c} ${name})`))

            for (let [i,v] of a.params.entries()) {
                let npid = `IProveParameter${SID.n++}`;
                let NPD = renderPattern(v, npid, t)
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
                let NPD = renderPattern(v, npid, t)
                R.push(mk_bind(`(${npid} (${getSelector(i)} ${name}))`))
                R = R.concat(NPD)
            }
            return R
        }
    }
}

export function renderNode(a: AST.ASTNode | undefined): string {
    if (!a) return "NULL";

    switch (a.kind) {
        case "PrimitiveType": return (a.ident == "Prop") ? "Bool" : a.ident;
        case "FunctionType": return `(${a.argTypes.map(renderNode).join(" ")})  ${renderNode(a.retType)}`;
        case "VariableBinding": return `(${renderNode(a.symbol)} ${a.type ? renderNode(a.type) : "Int"})`;
        case "FunctionDeclaration": return `(declare-fun ${a.symbol} ${renderNode(a.type)})`;
        case "SortDeclaration": return `(declare-sort ${renderNode(a.symbol)} ${a.arity})`;
        case "VariableDeclaration": return `(declare-const ${renderNode(a.symbol)} ${a.type ? `${renderNode(a.type)}` : "Int"})`;
        case "Variable": return (a.ident == "otherwise") ? "true" : a.ident;
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
                case "ArraySelect":
                    return `(ListElem ${a.params.map(renderNode).join(" ")})`
                case "ArraySlice":
                    return `(ListSlice ${a.params.map(renderNode).join(" ")} nil)`
                case "++":
                    return `(ListConcat ${a.params.map(renderNode).join(" ")})`
                case ":":
                    return `(IProveInsert ${a.params.map(renderNode).join(" ")})`
                case "in":
                    if (!a.params[1] 
                        || a.params[1].kind != "Variable") return "false"
                    return `(${a.params[1].ident} ${renderNode(a.params[0])})`
                default:
                    return (a.params.length)
                    ? `(${fnSMT(a.fn)} ${a.params.map(renderNode).join(" ")})`
                    : fnSMT(a.fn)
            }
        }
        case "QuantifierApplication": {
            let precons: AST.FunctionApplication[] = a.vars.filter((v) => !(!v.bound)).map((v) => ({
                kind: "FunctionApplication",
                appType: "InfixOp",
                fn: ">=",
                params: [v.symbol, mk_var(`${v.bound}`)]
            }))
            let final_term = precons.length
                ? (a.quantifier === "E" 
                    ? conjunct([a.term].concat(precons))
                    : imply(conjunct(precons), a.term))
                : a.term
            return `(${a.quantifier === "E" ? "exists" : "forall"} (${a.vars.map(renderNode).join(" ")}) ${renderNode(final_term)})`
        };
        case "EquationTerm": return `${renderNode(a.lhs)} ::= ${renderNode(a.rhs)}`;
        case "ParenTerm": return renderNode(a.term);
    
        case "TypeDef": {
            let cons = a.cases.map(renderNode).join(" ");
            return `(${a.ident} ${cons})`
        }
        case "TypeConstructor": {
            let params = a.params.map(
                (e, i) => (`(${a.selectors[i]} ${renderNode(e)})`));
            return (params.length)
                ? `(${a.ident} ${params.join(" ")})`
                : a.ident
        }

        case "ParamType":
            return `(${a.ident == "List" ? "IProveList" : a.ident} ${a.params.map(renderNode).join(" ")})`
        case "ListType":
            return `(IProveList ${renderNode(a.param)})`
        case "TupleType": {
            let N = a.params.length;
            LI.createTuple(N);
            return `(IProveTuple${N} ${a.params.map(renderNode).join(" ")})`;
        }
        
        case "ArrayLiteral": {
            //let R = `(as nil (IProveList ${LI.deriveType(a.elems[0])}))`;
            let R = "nil"
            for (let e of a.elems.reverse())
                R = `(IProveInsert ${renderNode(e)} ${R})`
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
