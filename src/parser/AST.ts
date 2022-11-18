import { render } from "@testing-library/react"

export type ASTNode = Type | FunctionType | VariableBinding | Line | Pattern | Guard | TypeConstructor

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
    params: [Term, Term?, Term?]
}

export type QuantifierApplication = {
    kind: "QuantifierApplication",
    term: Term,
    vars: VariableBinding[],
    quantifier: "E" | "A"
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
        this.rendered_givens;
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
    combineTerms(ts: Term[], conjunct: boolean = false): Term | undefined {
        let A = ts.shift();
        if (!A) return undefined;
        let tail = this.combineTerms(ts, conjunct);
        if (!tail) return A;

        return {
            kind: "FunctionApplication",
            appType: "InfixOp",
            fn: conjunct ? "&" : "||",
            params: [A, tail]
        }
    }
    disjunct = this.combineTerms
    conjunct = (ts: Term[]): Term | undefined => (this.combineTerms(ts, true))

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
            case "FunctionApplication": return `(${fnSMT(a.fn)} ${a.params.map(this.renderNode, this).join(" ")})`;
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
                return `(${a.ident} ${params.join(" ")})`
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
            res += `(assert ${v})\n`

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
}

export const LI = new LogicInterface();
export const ASTSMTLIB2: (line: Line | undefined) => string = LI.ast2smtlib;
