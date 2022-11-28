import { kMaxLength } from "buffer"

export type ASTNode = Type | FunctionType | VariableBinding | Line | Pattern | TypeConstructor | Guard

export type TypeDef = {
    kind: "TypeDef",
    ident: string,
    params: string[],
    cases: TypeConstructor[]
}

export type TypeConstructor = {
    kind: "TypeConstructor",
    ident: string,
    params: Type[],
    selectors: string[]
}

export type Tactic = Assumption | Skolemize | BeginScope | EndScope
export type Assumption = {
    kind: "Assumption",
    arg: Term
}
export type Skolemize = {
    kind: "Skolemize",
    arg: string
}
export type BeginScope = {
    kind: "BeginScope"
}
export type EndScope = {
    kind: "EndScope"
}

export type FunctionDefinition = {
    kind: "FunctionDefinition",
    ident: string,
    params: Pattern[],
    def: Guard | Term
}

export type Guard = {
    kind: "Guard",
    cond: Term,
    res: Term,
    next: Guard | undefined
}

export type Pattern = SimpleParam | ConsParam | EmptyList | ConstructedType | TuplePattern
export type SimpleParam = {
    kind: "SimpleParam",
    ident: string
}
export type ConsParam = {
    kind: "ConsParam",
    A: string,
    B: string
}
export type EmptyList = {
    kind: "EmptyList"
}
export type ConstructedType = {
    kind: "ConstructedType",
    c: string,
    params: Pattern[]
}
export type TuplePattern = {
    kind: "TuplePattern",
    params: Pattern[]
}

export type Type = PrimitiveType | ParamType | ListType | TupleType
export type PrimitiveType = { 
    kind: "PrimitiveType",
    ident: string
}
export type ParamType = { 
    kind: "ParamType",
    ident: string,
    params: Type[]
}
export type ListType = { 
    kind: "ListType",
    param: Type
}
export type TupleType = {
    kind: "TupleType",
    params: Type[]
}

export type FunctionType = {
    kind: "FunctionType",
    argTypes: Type[],
    retType: Type
}

export type VariableBinding = {
    kind: "VariableBinding",
    symbol: Variable,
    type?: Type
}
export type BlockStart = VariableDeclaration | Assumption | BeginScope;
export type Line = TypeExt | Declaration | Term | Tactic | FunctionDefinition | TypeDef

export type TypeExt = {
    kind: "TypeExt",
    subType: Type,
    superType: Type
}

export type Declaration = FunctionDeclaration | VariableDeclaration

export type FunctionDeclaration = {
    kind: "FunctionDeclaration",
    symbol: string,
    type: FunctionType
}

export type VariableDeclaration = {
    kind: "VariableDeclaration",
    symbol: Variable,
    type?: Type
}

export type Term = Variable | FunctionApplication | QuantifierApplication | EquationTerm | ParenTerm | ArrayLiteral

export type FunctionApplication = PrefixApplication | UnaryApplication | InfixApplication | ArrayElem | ArraySlice

export type AppType = FunctionApplication["appType"]

export type Variable = { 
    kind: "Variable",
    ident: string
}

export type ArrayLiteral = {
    kind: "ArrayLiteral",
    elems: Term[]
}

export type PrefixApplication = {
    kind: "FunctionApplication",
    appType: "PrefixFunc" | "PrefixOp",
    fn: string,
    params: Term[]
}

export type UnaryApplication = {
    kind: "FunctionApplication",
    appType: "UnaryFunc" | "UnaryOp",
    fn: string,
    params: [Term]
}

export type InfixApplication = {
    kind: "FunctionApplication",
    appType: "InfixFunc" | "InfixOp",
    fn: string,
    params: [Term, Term]
}

export type ArrayElem = {
    kind: "FunctionApplication",
    appType: "ArrayElem",
    fn: "select",
    params: [Term, Term]
}

export type ArraySlice = {
    kind: "FunctionApplication",
    appType: "ArraySlice",
    fn: "???", // TODO
    params: [Term, Term] | [Term, Term, Term]
}

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: VariableBinding[],
    quantifier: "E" | "A",

    var_nesting?: number[]
}

export type EquationTerm = {
    kind: "EquationTerm",
    lhs: Term,
    rhs: Term
}

export type ParenTerm = { 
    kind: "ParenTerm",
    term: Term
}

function fnDisplay(fn: string): string {
    switch (fn) {
        case "~": return "¬"; 
        case "&": return "∧";
        case "|": return "∨";
        case "^": return "⊕";
        case "->": return "→";
        case "<->": return "↔";
        default: return fn;
    }
}

function fnSMT(fn: string): string {
    switch (fn) {
        case "~": return "not";
        case "&": return "and";
        case "|": return "or";
        case "^": return "xor";
        case "->": return "implies";
        case "<->": return "=";
        default: return fn;
    }
}

function d(a: ASTNode): string {
    switch (a.kind) {
        case "PrimitiveType": return a.ident;
        case "FunctionType": return `(${a.argTypes.map(d).join(", ")}) -> ${d(a.retType)}`;
        case "TypeExt": return `${d(a.subType)} ⊆ ${d(a.superType)}`;
        case "VariableBinding": return d(a.symbol) + (a.type ? `: ${d(a.type)}` : "");
        case "FunctionDeclaration": return `${a.symbol} :: ${d(a.type)}`;
        case "VariableDeclaration": return `var ${d(a.symbol)}` + (a.type ? `: ${d(a.type)}` : "");
        case "Variable": return a.ident;
        case "FunctionApplication": {
            const fn = fnDisplay(a.fn);
            switch (a.appType) {
                case "PrefixFunc": return `${fn}(${a.params.map(d).join(", ")})`;
                case "PrefixOp": return `(${fn})(${a.params.map(d).join(", ")})`;
                case "InfixFunc": return `${d(a.params[0])} \`${fn}\` ${d(a.params[1])}`;
                case "InfixOp": return `${d(a.params[0])} ${fn} ${d(a.params[1])}`;
                case "UnaryFunc": return `$\`${fn}\` ${d(a.params[0])}`;
                case "UnaryOp": return `${fn} ${d(a.params[0])}`;
                case "ArrayElem": return `${d(a.params[0])}[${d(a.params[1])}]`;
                case "ArraySlice": {
                    const p1 = (a.params[1]) ? d(a.params[1]) : "";
                    const p2 = (a.params[2]) ? d(a.params[2]) : "";
                    return `${d(a.params[0])}[${p1}..${p2})`;
                }
            }
        }
        case "QuantifierApplication": return `${a.quantifier === "E" ? "∃" : "∀"}(${a.vars.map(d).join(",")}).${d(a.term)}`;
        case "EquationTerm": return `${d(a.lhs)} ::= ${d(a.rhs)}`;
        case "ParenTerm": return `[${d(a.term)}]`;
        
        case "BeginScope": return "begin";
        case "EndScope": return "end";
        case "Assumption": return `assume ${d(a.arg)}`;
        case "Skolemize": return `skolem ${a.arg}`;

        case "FunctionDefinition":
            return `${a.ident} ${a.params.map(d).join(" ")} ::= ${d(a.def)}` 
        case "Guard": return `\n  | ${a.cond} := ${a.res}`
        case "SimpleParam": return `${a.ident}`
        case "ConsParam": return `(${a.A}::${a.B})`
        case "EmptyList": return "[]"
        case "ConstructedType": 
            return `(${a.c} ${a.params.map(d).join(" ")})` 
        case "TuplePattern":
            return `(${a.params.map(d).join(", ")})` 
        
        case "TypeDef": return `type ${a.ident} ::= ${a.cases.map(d).join(" | ")}`
        case "TypeConstructor": return `${a.ident} ${a.params.map(d).join(" ")}` 

        case "ParamType": return `${a.ident}<${a.params.map(d).join(",")}>`
        case "ListType": return `[${d(a.param)}]`
        case "TupleType": return `(${a.params.map(d).join(", ")})`

        case "ArrayLiteral": return `{ ${a.elems.map(d).join(", ")} }`
    }
}


export const display: (line: Line) => string = d

export const isBlockStart = (line: Line): line is BlockStart => {
return line.kind === "BeginScope" || line.kind === "VariableDeclaration" || line.kind === "Assumption";
}

export const isBlockEnd = (line: Line): line is EndScope => {
return line.kind === "EndScope";
}

export const toWrapperFunc = (w: BlockStart): ((term: Term) => Term) => {
if (w.kind === "VariableDeclaration") {
    return term => ({
    kind: "QuantifierApplication",
    quantifier: "A",
    vars: [{
        kind: "VariableBinding",
        symbol: w.symbol,
        type: w.type
    }],
    term
    });
} else if (w.kind === "Assumption") {
    return term => ({
    kind: "FunctionApplication",
    appType: "InfixOp",
    fn: "=>",
    params: [w.arg, term]
    });
} else if (w.kind === "BeginScope") {
    return term => term
} throw "unsupported BlockStart"; // why isn't this unreachable
}

export const isTerm = (line: Line): line is Term => {
return line.kind === "Variable"
    || line.kind === "FunctionApplication"
    || line.kind === "QuantifierApplication"
    || line.kind === "EquationTerm"
    || line.kind === "ParenTerm"
}

export type PatternData = {
    conditions: string[],
    bindings: string[]
}

export type FunctionData = {
    decl: FunctionDeclaration | undefined,
    cid: number,
    defs: Map<number, FunctionDefinition>
}

export class LogicInterface {
    // persist after reset
    globals: Map<number, ASTNode> = new Map();
    rendered_globals: Map<number, string> = new Map();
    rendered_tuples: Map<number, string> = new Map();
    functions: Map<string, FunctionData> = new Map();
    insID: number = 0;


    // change on reset
    givens: ASTNode[] = [];
    goal: ASTNode | undefined;
    rendered_givens: string[] = [];
    rendered_goal: string | undefined;

    listID: number = 0;

    // Call this method before setting givens and goal for the current
    // proof
    newProof(): void {
        this.listID = 0
        this.goal = undefined;
        this.givens = [];

        this.rendered_goal = undefined;
        this.rendered_givens = [];

        this.globals = new Map();
        this.rendered_globals = new Map();
        this.rendered_tuples = new Map();
        this.functions = new Map();
        this.insID = 0;
    }

    renderGlobal(id: number): boolean {
        let A = this.globals.get(id);
        if (!A) return false;

        this.rendered_globals.set(
            id,
            this.renderNode(A)
        )
        return true;
    }

    // Add a global given. Returns the item ID (used for removing in future)
    addGlobal(n: ASTNode): number | undefined {
        let cID = this.insID++;
        this.globals.set(cID, n);
        this.renderGlobal(cID);
        return cID;
    }

    // Remove a global given by ID. Returns true iff successfully removed
    removeGlobal(n: number): boolean {
        return this.globals.delete(n) && this.rendered_globals.delete(n);
    }

    // Add instance given
    addGiven(n: ASTNode): boolean {
        this.givens.push(n)
        return true;
    }

    // Set the instance goal. Returns the previous one. Note that if we were
    // to stack goals P, Q, by De Morgan this is exactly setting the goal to
    // P || Q, so we force this instead to increase usability.
    //
    // For now, we do not allow function definitions as goals. This would
    // be useful sugar in proving the equivalence of function definitions
    // but also a bit trickier and not encountered in 1/2 year.
    setGoal(n: Term): ASTNode | undefined {
        let old = this.goal;
        this.goal = n;
        return old
    }

    // utility rec function which takes in an array of terms and returns their
    // (left-associative) dis(/con)junction. See above comment to motivate existence.
    combineTerms(ts: Term[], conjunct: string = "||"): Term | undefined {
        let A = ts.shift();
        if (!A) return undefined;
        let tail = this.combineTerms(ts, conjunct);
        if (!tail) return A;

        return {
            kind: "FunctionApplication",
            appType: "InfixOp",
            fn: conjunct,
            params: [A, tail]
        }
    }
    disjunct = this.combineTerms
    conjunct = (ts: Term[]): Term | undefined => (this.combineTerms(ts, "&"))

    // Adds tuples of particular length to the global context. Returns true
    // iff the tuple length wasn't already handled
    getSelector(n: number): string {
        switch (n) {
            case 1: return "fst";
            case 2: return "snd";
            default: return `elem${n}`;
        }
    }
    createTuple(n: number): boolean {
        if (this.rendered_tuples.has(n)) return false;

        let thisID = `IProveTuple${n}`
        let elems: string[] = [];
        let params: string[] = [];
        for (let i = 1; i <= n; i++) {
            params.push(`PT${i}`)
            elems.push(`(${this.getSelector(i)} PT${i})`)
        }

        this.rendered_tuples.set(n,
            `(declare-datatypes (${params.join(" ")}) ((${thisID} (mk-tuple ${elems.join(" ")}))))`
        )
        return true;
    }


    renderPattern(a: Pattern, name: string): PatternData {
        switch(a.kind) {
            case "SimpleParam":
                return { conditions: [], bindings: [`(${a.ident} ${name})`] }
            case "ConsParam":
                return {
                    conditions: [`(> (seq.len ${name}) 0)`],
                    bindings: [
                        `(${a.A} (seq.nth ${name} 0))`,
                        `(${a.B} (seq.extract ${name} 1 (- (seq.len ${name}) 1)))`]
                }
            case "EmptyList":
                return { conditions: [`(= (seq.len ${name}) 0)`], bindings: [] }
            case "ConstructedType":
                return { conditions: [], bindings: [] }
            case "TuplePattern":
                return { conditions: [], bindings: [] }
        }
    }

    renderFunction(ident: string): string | undefined {
        let A = this.functions.get(ident);
        if (!A || !A.decl) return undefined;

        if (!A.defs.size) {
            return this.renderNode(A.decl);
        }

        let params: string[] = []
        let nparams = A.decl.type.argTypes.length;

        for (let i = 0; i < nparams; i++)
            params.push(`IProveParameter${i}`)

        let pdatas: [PatternData, Term][] = [];
        for (let [i, a] of A.defs) {
            if (a.params.length != nparams) return undefined;

            let idx: number = 0;
            for (let p of a.params) {
                pdatas.push([
                    this.renderPattern(p, `IProveParameter${idx}`),
                    (a.def as Term)
                ]);
                idx++;
            }
        }

        let sections: string[] = [];
        for (let [p, d] of pdatas) {
            let cond = (p.conditions.length)
                ? p.conditions[0]
                : "true";
            let bindings: string = (p.bindings.length)
                ? `(let (${p.bindings.join(" ")}) ${this.renderNode(d)})`
                : this.renderNode(d);
            sections.push(`(if ${cond} ${bindings}`)
        }
        sections.push("0");
        let defn: string = sections.join(" ");
        for (let i = 0; i < sections.length - 1; i++)
            defn += ")";

        let rendered_params: string[] = [];
        for (let i = 0; i < nparams; i++)
            rendered_params.push(`(${params[i]} ${this.renderNode(A.decl.type.argTypes[0])})`)
        
        let type = `(${rendered_params.join(" ")}) ${this.renderNode(A.decl.type.retType)}`
        return `(define-fun-rec ${ident} ${type} ${defn})`
    }

    newFunction(ident: string): boolean {
        if (this.functions.has(ident))
            return false;
        
        this.functions.set(ident, {
            decl: undefined,
            cid: 0,
            defs: new Map()
        })
        return true;
    }

    addFnDecl(a: FunctionDeclaration): FunctionDeclaration | undefined {
        this.newFunction(a.symbol);
        let A = this.functions.get(a.symbol);
        if (!A) return undefined; // error case for typechecking

        let old = A.decl;
        A.decl = a;
        return old;
    }

    // Adds a function definition and returns its id within the definition of
    // this particular function
    addFnDef(a: FunctionDefinition): number {
        this.newFunction(a.ident);

        let A = this.functions.get(a.ident);
        if (!A) return 0 // error case for typechecking

        A.defs.set(++A.cid, a)
        return A.cid;
    }

    // If id is null, the entire function will be removed, otherwise
    // just the definition given by id
    removeFnDef(ident: string, id: number | null = null): boolean {
        if (!id)
            return this.functions.delete(ident);
        
        let A = this.functions.get(ident);
        if (!A) return false;
        return A.defs.delete(id);
    }

    renderNode(a: ASTNode | undefined): string {
        if (!a) return "NULL";

        switch (a.kind) {
            case "PrimitiveType": return a.ident;
            case "FunctionType": return `(${a.argTypes.map(this.renderNode, this).join(" ")})  ${this.renderNode(a.retType)}`;
            case "VariableBinding": return `(${this.renderNode(a.symbol)} ${a.type ? this.renderNode(a.type) : "Int"})`;
            case "TypeExt": return `${this.renderNode(a.subType)} ⊆ ${this.renderNode(a.superType)}`;
            case "FunctionDeclaration": return `(declare-fun ${a.symbol} ${this.renderNode(a.type)})`;
            case "VariableDeclaration": return `(declare-const ${this.renderNode(a.symbol)} ${a.type ? `${this.renderNode(a.type)}` : "Int"})`;
            case "Variable": return a.ident;
            case "FunctionApplication":
                return (a.params.length)
                    ? `(${fnSMT(a.fn)} ${a.params.map(this.renderNode, this).join(" ")})`
                    : fnSMT(a.fn)
            case "QuantifierApplication": return `(${a.quantifier === "E" ? "exists" : "forall"} (${a.vars.map(this.renderNode, this).join(" ")}) ${this.renderNode(a.term)})`;
            case "EquationTerm": return `${this.renderNode(a.lhs)} ::= ${this.renderNode(a.rhs)}`;
            case "ParenTerm": return this.renderNode(a.term);
        
            case "TypeDef": {
                let cons = a.cases.map(this.renderNode, this).join(" ");
                let type_params = a.params.join(" ");
                return `(declare-datatypes (${type_params}) ((${a.ident} ${cons})))`
            }
            case "TypeConstructor": {
                let params = a.params.map(
                    (e, i) => (`(${a.selectors[i]} ${this.renderNode(e)})`));
                return (params.length)
                    ? `(${a.ident} ${params.join(" ")})`
                    : a.ident
            }

            case "ParamType":
                return `(${a.ident} ${a.params.map(this.renderNode, this).join(" ")})`
            case "ListType":
                return `(Seq ${this.renderNode(a.param)})`
            case "TupleType": {
                let N = a.params.length;
                this.createTuple(N);
                return `(IProveTuple${N} ${a.params.map(this.renderNode, this).join(" ")})`;
            }
            
            case "ArrayLiteral": {
                let units = a.elems.map((e) => 
                    (`(seq.unit ${this.renderNode(e)})`), this);
                return `(seq.++ ${units.join(" ")})`
            }

            // THESE CASES NEED TO BE HANDLED SOMEHOW?
            case "BeginScope":
            case "EndScope":
            case "Assumption":
            case "Skolemize":
                return "";
            // ^^
            
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

    // LEGACY DONT USE
    ast2smtlib(a: ASTNode | undefined) : string {
        if(a === undefined) return "NULL"
        var ancillae: string[] = []
        let renderedNode: string = this.renderNode(a)
        let mapped = (ancillae.length)
            ? `${ancillae.join("\n")}\n`
            : "";
        return `${mapped}${renderedNode}`
    }

    toString(): string {
        let res = "";

        // TUPLES
        for (let [k, v] of this.rendered_tuples)
            res += `${v}\n`

        // FUNCTIONS
        for (let [k,v] of this.functions)
            res += `${this.renderFunction(k)}\n`

        // GLOBALS
        for (let [k,v] of this.rendered_globals)
            res += v.startsWith("(declare-") ? `${v}\n` : `(assert ${v})\n`

        // GIVENS
        for (let v of this.givens) {
            switch (v.kind) {
                case "VariableDeclaration":
                case "FunctionDeclaration":
                    res += this.renderNode(v); break;
                default:
                    res += `(assert ${this.renderNode(v)})`

            }
            res += "\n"
        }

        // GOAL
        res += `(assert (not ${this.renderNode(this.goal)}))\n`

        return res;
    }

    //rec_on(t: TypeDef): (x: Variable)
}


// Given a function f: Term -> Term, returns a function which, given an AST A,
// returns the AST corresponding to a recursive application of f to the terms
// of A.
export type StatefulTransformer<T, S> = (x: T, st: S) => [T, S]
export function map_terms<T>(f: StatefulTransformer<Term, T>, init: T, lazy: boolean = false): (A: Term) => [Term, T] {
    var R: StatefulTransformer<ASTNode, T>
    var RT: (A: Term, st: T, seen?: boolean) => [Term, T]
    var RG: StatefulTransformer<Guard, T>
    var RGT: StatefulTransformer<Guard | Term, T>
    var RT_ = (t: Term | undefined, st: T): [Term | undefined, T] =>
        (t ? RT(t, st, false) : [undefined, st]);
    var RG_ = (t: Guard | undefined, st: T): [Guard | undefined, T] =>
        (t ? RG(t, st) : [undefined, st]);

    
    R = (A: ASTNode, st: T): [ASTNode, T] => {
        switch (A.kind) {
            // ARE TERMS AND CAN CONTAIN THEM
            case "FunctionApplication":
            case "QuantifierApplication":
            case "EquationTerm":
            case "ParenTerm":
            case "ArrayLiteral":
            case "Variable":
                return RT(A, st, false)

            // NOT A TERM, BUT CAN CONTAIN THEM
            case "Guard":
                return RG(A, st);
            case "Assumption": {
                let [new_A, new_st] = RT(A.arg, st, false)
                return [{
                    kind: "Assumption",
                    arg: new_A
                }, new_st]
            } case "FunctionDefinition": {
                let [new_A, new_st] = RGT(A.def, st)
                return [{
                    kind: "FunctionDefinition",
                    ident: A.ident,
                    params: A.params,
                    def: new_A
                }, new_st]
            }

            // NEITHER TERMS NOR CAN CONTAIN THEM
            case "PrimitiveType":
            case "FunctionType":
            case "VariableBinding":
            case "TypeExt": 
            case "FunctionDeclaration":
            case "VariableDeclaration":
            case "TypeDef":
            case "TypeConstructor":
            case "ParamType":
            case "ListType":
            case "TupleType":
            case "BeginScope":
            case "EndScope":
            case "Skolemize":
            case "SimpleParam":
            case "ConsParam":
            case "ConstructedType":
            case "EmptyList":
            case "TuplePattern":
                return [A, st];
            
        }
    }

    RG = (A: Guard, st_0: T): [Guard, T] => {
        let [new_cond, st_1] = RT(A.cond, st_0, false)
        let [new_res, st_2] = RT(A.res, st_1, false)
        let [new_next, st_3] = RG_(A.next, st_2)
        return [{
            kind: "Guard",
            cond: new_cond,
            res: new_res,
            next: new_next
        }, st_3]
    }

    RGT = (A: Guard | Term, st: T): [Guard | Term, T] => {
        switch (A.kind) {
            case "FunctionApplication":
            case "QuantifierApplication":
            case "EquationTerm":
            case "ParenTerm":
            case "ArrayLiteral":
            case "Variable":
                return RT(A, st)

            case "Guard":
                return RG(A, st);
        }
    }

    function stateful_map<X, Y, S>(f: (x: X, s: S) => [Y, S]): (x: X[], s: S) => [Y[], S] {
        return (x: X[], s: S): [Y[], S] => {
            let R: Y[] = [];
            let c_s: S = s;
            let me: Y;
            for (let e of x) {
                [me, c_s] = f(e, c_s)
                R.push(me)
            }
            return [R, c_s]
        }
    }

    RT = (A: Term, st: T, seen?: boolean): [Term, T] => {
        if (!lazy) {
            switch (A.kind) {
                // ARE TERMS AND CAN CONTAIN THEM
                case "FunctionApplication":
                    // I HATE TYPESCRIPT I HATE TYPESCRIPT
                    switch (A.appType) {
                        case "PrefixFunc":
                        case "PrefixOp": {
                            let [new_params, new_st] = stateful_map(RT)(A.params, st)
                            return f({
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: new_params
                            }, new_st);
                        }
                        case "UnaryFunc":
                        case "UnaryOp": {
                            let [new_param, new_st] = RT(A.params[0], st)
                            return f({
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param]
                            }, new_st);
                        }
                        case "InfixFunc":
                        case "InfixOp": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            return f({
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param_1, new_param_2]
                            }, st_2);
                        }
                        case "ArrayElem": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            return f({
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param_1, new_param_2]
                            }, st_2);
                        }
                        
                        case "ArraySlice": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            let [new_param_3, st_3] = RT_(A.params[2], st_2)
                            let new_params : [Term, Term, Term] | [Term, Term]
                                = (new_param_3)
                                    ? [new_param_1, new_param_2, new_param_3]
                                    : [new_param_1, new_param_2]
                            return f({
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: new_params
                            }, st_3);
                        }
                    }
                case "QuantifierApplication": {
                    let [new_term, new_st] = RT(A.term, st)
                    return f({
                        kind: "QuantifierApplication",
                        term: new_term,
                        vars: A.vars,
                        quantifier: A.quantifier
                    }, new_st)
                } case "EquationTerm": {
                    let [new_lhs, st_1] = RT(A.lhs, st)
                    let [new_rhs, st_2] = RT(A.rhs, st_1)
                    return f({
                        kind: "EquationTerm",
                        lhs: new_lhs,
                        rhs: new_rhs
                    }, st_2)
                } case "ParenTerm": {
                    let [new_term, new_st] = RT(A.term, st)
                    return f({
                        kind: "ParenTerm",
                        term: new_term
                    }, new_st)
                } case "ArrayLiteral": {
                    let [new_elems, new_st] = stateful_map(RT)(A.elems, st)
                    return f({
                        kind: "ArrayLiteral",
                        elems: new_elems
                    }, new_st)
                }
                
                // CANNOT CONTAIN TERMS, BUT IS ONE
                case "Variable":
                    return f(A, st)
            }
        } else {
            if (!seen) {
                let [new_node, new_st] = f(A, st)
                return RT(new_node, new_st, true)
            }
            switch (A.kind) {
                // ARE TERMS AND CAN CONTAIN THEM
                case "FunctionApplication":
                    // I HATE TYPESCRIPT I HATE TYPESCRIPT
                    switch (A.appType) {
                        case "PrefixFunc":
                        case "PrefixOp": {
                            let [new_params, new_st] = stateful_map(RT)(A.params, st)
                            return [{
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: new_params
                            }, new_st];
                        }
                        case "UnaryFunc":
                        case "UnaryOp": {
                            let [new_param, new_st] = RT(A.params[0], st)
                            return [{
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param]
                            }, new_st];
                        }
                        case "InfixFunc":
                        case "InfixOp": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            return [{
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param_1, new_param_2]
                            }, st_2];
                        }
                        case "ArrayElem": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            return [{
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: [new_param_1, new_param_2]
                            }, st_2];
                        }
                        
                        case "ArraySlice": {
                            let [new_param_1, st_1] = RT(A.params[0], st)
                            let [new_param_2, st_2] = RT(A.params[1], st_1)
                            let [new_param_3, st_3] = RT_(A.params[2], st_2)
                            let new_params : [Term, Term, Term] | [Term, Term]
                                = (new_param_3)
                                    ? [new_param_1, new_param_2, new_param_3]
                                    : [new_param_1, new_param_2]
                            return [{
                                kind: "FunctionApplication",
                                appType: A.appType,
                                fn: A.fn,
                                params: new_params
                            }, st_3];
                        }
                    }
                case "QuantifierApplication": {
                    let [new_term, new_st] = RT(A.term, st)
                    return [{
                        kind: "QuantifierApplication",
                        term: new_term,
                        vars: A.vars,
                        quantifier: A.quantifier
                    }, new_st]
                } case "EquationTerm": {
                    let [new_lhs, st_1] = RT(A.lhs, st)
                    let [new_rhs, st_2] = RT(A.rhs, st_1)
                    return [{
                        kind: "EquationTerm",
                        lhs: new_lhs,
                        rhs: new_rhs
                    }, st_2]
                } case "ParenTerm": {
                    let [new_term, new_st] = RT(A.term, st)
                    return [{
                        kind: "ParenTerm",
                        term: new_term
                    }, new_st]
                } case "ArrayLiteral": {
                    let [new_elems, new_st] = stateful_map(RT)(A.elems, st)
                    return [{
                        kind: "ArrayLiteral",
                        elems: new_elems
                    }, new_st]
                }
                
                // CANNOT CONTAIN TERMS, BUT IS ONE
                case "Variable":
                    return [A, st]
            }
        }
    }

    return (x: Term) => RT(x, init);
}

export function stateless_map_terms(f: (x: Term) => Term): (x: Term) => Term {
    //console.log(MT)
    let MT = map_terms((x: Term, st) => ([f(x), undefined]), undefined)
    return (x: Term) => {
        //console.log(x)
        return MT(x)[0];
    }
}

// NOTE: For obvious reasons, this will not rewrite in itself. 
export function strict_rw(goal: Term, L: Term, R: Term): Term {
    let f = (x: Term): Term => {
        let term_equal: Boolean = JSON.stringify(L) == JSON.stringify(x);
        return term_equal ? R : x
    }
    return stateless_map_terms(f)(goal);
}

class IdentState {
    cid: number = 0;
    get(): number {
        return this.cid++;
    }
}

function construct_type(con: TypeConstructor, params: Variable[]): PrefixApplication {
    return {
        kind: "FunctionApplication",
        appType: "PrefixFunc",
        fn: con.ident,
        params: params
    }
}

function mk_var(ident: string): Variable {
    return {
        kind: "Variable",
        ident: ident
    }
}

function range_over(t: Term, vars: [Variable, Type][]): Term {
    return vars.length ?
    {
        kind: "QuantifierApplication",
        term: parenthesize(t),
        vars: vars.map((v: [Variable, Type]) => ({
            kind: "VariableBinding",
            symbol: v[0],
            type: v[1]
        })),
        quantifier: "A"
    }
    : t
}

function imply(L: Term | undefined, R: Term): Term {
    if (!L) return R;
    return {
        kind: "FunctionApplication",
        appType: "InfixOp",
        fn: "->",
        params: [parenthesize(L), parenthesize(R)]
    }
}
export function parenthesize(t: Term): ParenTerm {
    return {
        kind: "ParenTerm",
        term: t
    }
}

export function rec_on(T: Type, type_def: TypeDef): (ident_: string, motive: Term) => Term {
    return (ident_: string, motive: Term): Term => {
        let ident: Variable = mk_var(ident_);

        let cases: Term[] = type_def.cases.map(con => {
            let vars: [Variable, Type][] = con.params.map(
                (v, i) => [mk_var(`InductiveParameter${i}`), v]
            );
            let subbed = strict_rw(motive, ident, construct_type(
                con,
                vars.map(x => x[0])
            ));

            let precons: Term[] = vars
                .filter(pt => pt[1] == T)
                .map(pt => strict_rw(motive, ident, pt[0]))
            let final_case: Term = imply(LI.conjunct(precons), subbed)
            
            return range_over(final_case, vars)
        })

        return imply(
            LI.conjunct(cases),
            range_over(motive, [[ident, T]]));
        }
}

// TODO: this function should be able to squash quantifiers down when what they
// quantify over only appears in one parameter of a function application
// but this requires leaf->root recursion over AST (or gross memoization :/)
// EDIT: Because JS isn't lazy, our recursion actually IS leaf-> root so now
// I've added a state to thread through this can get refactored
function squash_quantifier(A: Term): Term {
    return (
        A.kind == "QuantifierApplication"
        && A.term.kind == "QuantifierApplication"
        && A.quantifier == A.term.quantifier
    ) ? {
        kind: "QuantifierApplication",
        term: A.term.term,
        vars: A.vars.concat(A.term.vars),
        quantifier: A.quantifier
    } : A
}
export const squash_quantifiers = stateless_map_terms(squash_quantifier)

const AssocOperators: Set<string> = new Set([
    "&",
    "||"
])

const CommOperators: Set<string> = new Set([
    "&",
    "||"
])

function seek_parens(A: Term): Term {
    let c_t: Term = A;
    while (c_t.kind == "ParenTerm") c_t = c_t.term
    return c_t
}

// An associative chain is any repeated application of associative binary
// operators. This function extracts them either with the ignore_parens
// flag set to false (in which case this simply flattens nested left-associative)
// applications), or true (in which case this flattens THROUGH parentheses).
//
// In the way we're using it, ignore_parens means that we are exploiting
// associativity of (& / | / +(over ints) / *(over ints)), whereas disabling
// it allows us to account for commutativity without exploiting associativity
function assoc_chain(A: Term, ignore_parens: Boolean = false): Term {
    return (
        A.kind == "FunctionApplication"
        && A.appType != "ArrayElem" && A.appType != "ArraySlice"
        && AssocOperators.has(A.fn)
    ) ? {
        kind: "FunctionApplication",
        appType: "PrefixOp",
        fn: A.fn,
        params: A.params.map((sub: Term): Term[] => {
            let w_sub: Term = (ignore_parens) ? seek_parens(sub) : sub
            return (w_sub.kind == "FunctionApplication"
                && w_sub.appType != "ArrayElem" && w_sub.appType != "ArraySlice"
                && A.fn == w_sub.fn)
            ? w_sub.params
            : [sub]
        }).flat()
    } : A
}
export function extract_assoc(ignore_parens: Boolean = false)
: (x: Term) => Term {
    return stateless_map_terms((x_: Term): Term => assoc_chain(x_, ignore_parens))
} 

// 0-ary functions can be normalized to variables
function variablize(A: Term): Term {
    return (A.kind == "FunctionApplication"
        && (A.appType == "PrefixFunc"
            || A.appType == "PrefixOp"
            || A.appType == "UnaryFunc"
            || A.appType == "UnaryOp")
        && (!A.params.length))
        ? {
           kind: "Variable",
           ident: A.fn
        }
        : A
}
export const normalize_constants = stateless_map_terms(variablize);

// Once in the AST, we can remove all unneccessary parens
function unparenthesize(A: Term): Term {
    return (A.kind == "ParenTerm")
        ? A.term
        : A
}
export const remove_parens = stateless_map_terms(unparenthesize)

type RenameState = Map<string, number>
function rename_vars(A: Term, S: RenameState): [Term, RenameState] {
    switch(A.kind) {
        case "ArrayLiteral":
        case "EquationTerm":
        case "FunctionApplication":
        case "ParenTerm":
            return [A, S]

        case "QuantifierApplication": {
            let nvd: VariableBinding[] = []
            for (let v of A.vars) {
                let VI = S.get(v.symbol.ident)
                if (VI && VI > 0) {
                    nvd.push({
                        kind: "VariableBinding",
                        symbol: mk_var(`IProveAlpha_${VI}_${v.symbol.ident}`),
                        type: v.type
                    })
                    S.set(v.symbol.ident, VI + 1)
                } else {
                    nvd.push({
                        kind: "VariableBinding",
                        symbol: mk_var(`IProveAlpha_0_${v.symbol.ident}`),
                        type: v.type
                    })
                    S.set(v.symbol.ident, 1)
                }
            }
            return [{
                kind: "QuantifierApplication",
                quantifier: A.quantifier,
                term: A.term,
                vars: nvd
            }, S]
        }
        case "Variable": {
            let VI = S.get(A.ident)
            if (VI && VI > 0)
                return [mk_var(`IProveAlpha_${VI - 1}_${A.ident}`), S]
            else
                return [A, S]
        }
    }
}

export function rename_pass(A: Term): Term
    { return map_terms(rename_vars, new Map, true)(A)[0]; }

export function basic_preprocess(A: Term): Term {
    return squash_quantifiers(
        rename_pass (
            normalize_constants(A)
        )
    )
}

export function unify_preprocess(A: Term): Term {
    return extract_assoc()(
        remove_parens(
            basic_preprocess(A)
        )
    )
}

function assoc_length(A: Term, c: number): [Term, number] {
    return [A, (A.kind == "FunctionApplication" && AssocOperators.has(A.fn))
        ? Math.max(A.params.length, c)
        : c]
}
const mapped_AL = map_terms(assoc_length, 0)
export const max_assoc_length = (x: Term): number => mapped_AL(x)[1]


export type Unification = UnifyFail | UnifyScope

export type UnifyFail = {
    kind: "UnifyFail"
}

const UNIFY_FAIL: UnifyFail = {
    kind: "UnifyFail"
}

function get_from_scope(S: UnifyScope, x: string): string | undefined {
    for (let ss of S.assignments) {
        if (ss.has(x)) return ss.get(x)
    }
}

function set_in_scope(S: UnifyScope, a: string, b: string): boolean {
    if (S.sort_ctx_a.get(a) != S.sort_ctx_b.get(b)) return false
    S.assignments[0].set(a, b)
    return true
}

function push_scope(S: UnifyScope): void {
    S.assignments.unshift(new Map)
}

function pop_scope(S: UnifyScope): void {
    S.assignments.shift()
}

export type UnifyScope = {
    kind: "UnifyScope";
    sort_ctx_a: Map<string, string>;
    sort_ctx_b: Map<string, string>;
    assignments: Map<string, string | undefined>[];
}

export function gen_unify(A: Term | undefined, B: Term | undefined, scope: UnifyScope): Unification {
    if (!A || !B) {
        return ((!A) && (!B))
            ? scope : UNIFY_FAIL
    }

    switch (A.kind) {
        case "ArrayLiteral": {
            if (B.kind != "ArrayLiteral"
                || A.elems.length != B.elems.length) return UNIFY_FAIL
            
            let c_v: Unification = scope;
            for (let i = 0; i < A.elems.length; i++) {
                c_v = gen_unify(A.elems[i], B.elems[i], c_v)
                if (c_v.kind == "UnifyFail") return UNIFY_FAIL
            }
            return c_v;
        }
        case "EquationTerm": {
            if (B.kind != "EquationTerm") return UNIFY_FAIL
            let lhs_verdict = gen_unify(A.lhs, B.lhs, scope)
            let rhs_verdict = gen_unify(A.rhs, B.rhs, scope)
            if (rhs_verdict.kind == "UnifyFail" || lhs_verdict.kind == "UnifyFail")
                return UNIFY_FAIL

            return scope
        }
        case "ParenTerm": {
            if (B.kind != "ParenTerm") return UNIFY_FAIL
            return gen_unify(A.term, B.term, scope)
        }
        case "Variable": {
            if (B.kind != "Variable") return UNIFY_FAIL

            if (!scope.sort_ctx_a.has(A.ident) || 
                !scope.sort_ctx_b.has(B.ident) )
                return (A.ident == B.ident) ? scope : UNIFY_FAIL

            if (!get_from_scope(scope, A.ident)) {
                let set_verdict = set_in_scope(scope, A.ident, B.ident);
                if (!set_verdict) return UNIFY_FAIL
            }

            return (get_from_scope(scope, A.ident) == B.ident)
                ? scope
                : UNIFY_FAIL
        }
        case "QuantifierApplication": {
            const util = require("util")
            
            if (B.kind != "QuantifierApplication"
                || B.quantifier != A.quantifier
                || B.vars.length != A.vars.length)
                return UNIFY_FAIL

            let type_cnts: Map<string, number> = new Map
            let d_ = (x: Type | undefined): string => {
                if (!x) return "any"
                return d(x)
            }
            for (let i = 0; i < A.vars.length; i++) {
                scope.sort_ctx_a.set(A.vars[i].symbol.ident, d_(A.vars[i].type))
                scope.sort_ctx_b.set(B.vars[i].symbol.ident, d_(B.vars[i].type))
                
                let tca: number | undefined = type_cnts.get(d_(A.vars[i].type))
                if (!tca) tca = 0
                type_cnts.set(d_(A.vars[i].type), tca + 1)
                let tcb: number | undefined = type_cnts.get(d_(B.vars[i].type))
                if (!tcb) tcb = 0
                type_cnts.set(d_(B.vars[i].type), tcb - 1)
            }

            //console.log(type_cnts)
            for (let [_,v] of type_cnts)
                if (v != 0) return UNIFY_FAIL

            return gen_unify(A.term, B.term, scope)
            
        }
        case "FunctionApplication": {
            let N = A.params.length
            if (B.kind != "FunctionApplication"
                || N != B.params.length
                || A.fn != B.fn) return UNIFY_FAIL
            
            if (!CommOperators.has(A.fn)) {
                for (let i = 0; i < A.params.length; i++) {
                    let c_v = gen_unify(A.params[i], B.params[i], scope)
                    if (c_v.kind == "UnifyFail") return UNIFY_FAIL
                }
                return scope
            }

            // repeating A/B cases to allow non-matching appTypes
            // in terms of prefix/infix
            if (A.appType == "ArrayElem"
                || A.appType == "ArraySlice"
                || A.appType == "UnaryFunc"
                || A.appType == "UnaryOp"
                || B.appType == "ArrayElem"
                || B.appType == "ArraySlice"
                || B.appType == "UnaryFunc"
                || B.appType == "UnaryOp")
                return UNIFY_FAIL
            
            return gen_unify_poss(0, A.params, B.params, 0, scope)
        }
    }
}

function bitmap_mex(bs: number, st: number = 0): number {
    bs = bs >> st
    let R = st;
    while (bs & 1) {
        R++;
        bs = bs >> 1;
    }
    return R
}

function set_bit(N: number, i: number): number {
    return N | (1 << i)
}

function gen_unify_poss(
    i: number,
    A: Term[],
    B: Term[],
    bitmap: number,
    scope: UnifyScope): Unification 
{
    if (i >= A.length) return scope

    let b_i: number | undefined = -1
    while (true) {
        b_i = bitmap_mex(bitmap, b_i + 1)
        if (b_i >= B.length) return UNIFY_FAIL

        push_scope(scope)
        if (gen_unify(A[i], B[b_i], scope).kind == "UnifyScope") {
            let res = gen_unify_poss(i + 1, A, B, set_bit(bitmap, b_i), scope)
            if (res.kind == "UnifyScope") return scope
        }
        pop_scope(scope)
    }
}

const alpha_regex: RegExp = /^IProveAlpha_(\d+)_/
function replace_var(M: Map<string, string>, unalpha: boolean = true): (A: Term) => Term {
    let MGet = (xi: string): string | undefined => 
        (unalpha) ? M.get(xi) : M.get(xi)?.replace(alpha_regex, '')
    return (A: Term): Term => {
        switch (A.kind) {
            case "ArrayLiteral":
            case "EquationTerm":
            case "FunctionApplication":
            case "ParenTerm":
                return A
            
            case "QuantifierApplication": {
                let VL: VariableBinding[] = []
                for (let vb of A.vars) {
                    let MG = MGet(vb.symbol.ident)
                    if (MG) {
                        VL.push({
                            kind: "VariableBinding",
                            symbol: mk_var(MG),
                            type: vb.type
                        })
                    }
                }
                return {
                    kind: "QuantifierApplication",
                    term: A.term,
                    quantifier: A.quantifier,
                    vars: VL
                }
            }
            case "Variable": {
                let MG = MGet(A.ident)
                if (MG) return mk_var(MG)
                return A
            }

        }
    }
}
function replace_vars(M: Map<string, string>, unalpha: boolean = false): (x: Term) => Term {
    return stateless_map_terms(replace_var(M, unalpha))
}

export type AlphaAssignment = {
    kind: "AlphaAssignment",
    assn: Map<string, string>,
    term: Term
}

export function unifies(A_: Term, B_: Term): AlphaAssignment | UnifyFail {
    let A: Term = unify_preprocess(A_)
    let B: Term = unify_preprocess(B_)

    let verdict: Unification = gen_unify(B, A, {
        kind: "UnifyScope",
        sort_ctx_a: new Map,
        sort_ctx_b: new Map,
        assignments: [new Map]
    })

    return (verdict.kind == "UnifyFail")
    ? verdict
    : { kind: "AlphaAssignment",
        term: replace_vars(verdict.assignments.reduce((x, y) => {
            return new Map([...y,...x])
        }, new Map()))(basic_preprocess(B_)),
        assn: verdict.assignments.reduce((x, y) => {
            return new Map([...y,...x])
        }, new Map()) }
}

export const LI = new LogicInterface();
export const ASTSMTLIB2: (line: Line | undefined) => string = LI.ast2smtlib;

