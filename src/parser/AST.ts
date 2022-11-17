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

export class LogicInterface {
    // persist after reset
    globals: Map<number, ASTNode> = new Map();
    rendered_globals: Map<number, string> = new Map();
    rendered_tuples: Map<number, string> = new Map();
    insID: number = 0;

    // change on reset
    givens: ASTNode[] = [];
    goal: ASTNode | undefined;
    rendered_givens: string[] = [];
    rendered_goal: string | undefined;


    functionDefinitions: Map<string, string> = new Map();
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

    renderPattern(a: Pattern): string {
        switch(a.kind) {
            case "SimpleParam":
            case "ConsParam":
            case "EmptyList":
            case "ConstructedType":
                return "";
            case "TuplePattern": {
                
            }
        }
    }

    renderNode(a: ASTNode | undefined): string {
        if (!a) return "NULL";

        let s = this.renderNode;
        switch (a.kind) {
            case "PrimitiveType": return a.ident;
            case "FunctionType": return `(${a.argTypes.map(s).join(" ")})  ${s(a.retType)}`;
            case "VariableBinding": return `(${s(a.symbol)} ${a.type ? s(a.type) : "Int"})`;
            case "TypeExt": return `${s(a.subType)} ⊆ ${s(a.superType)}`;
            case "FunctionDeclaration": return `(declare-fun ${a.symbol} ${s(a.type)})`;
            case "VariableDeclaration": return `(declare-const ${s(a.symbol)} ${a.type ? `${s(a.type)}` : "Int"})`;
            case "Variable": return a.ident;
            case "FunctionApplication": return `(${fnSMT(a.fn)} ${a.params.map(s).join(" ")})`;
            case "QuantifierApplication": return `(${a.quantifier === "E" ? "exists" : "forall"} (${a.vars.map(s).join(" ")}) ${s(a.term)})`;
            case "EquationTerm": return `${s(a.lhs)} ::= ${s(a.rhs)}`;
            case "ParenTerm": return s(a.term);

            case "BeginScope":
            case "EndScope":
            case "Assumption":
            case "Skolemize":
                return "";

            case "FunctionDefinition":
            case "Guard":
            case "SimpleParam":
            case "ConsParam":
            case "EmptyList":
            case "ConstructedType":
                return "";
            case "TuplePattern": {
                a.
            }
            
            case "TypeDef": {
                let cons = a.cases.map(s).join(" ");
                let type_params = a.params.join(" ");
                return `(declare-datatypes (${type_params}) ((${a.ident} ${cons})))`
            }
            case "TypeConstructor": {
                let params = a.params.map(
                    (e, i) => (`(${a.selectors[i]} ${s(e)})`));
                return `(${a.ident} ${params.join(" ")})`
            }

            case "ParamType":
                return `(${a.ident} ${a.params.map(s).join(" ")})`
            case "ListType":
                return `(Seq ${s(a.param)})`
            case "TupleType": {
                let N = a.params.length;
                this.createTuple(N);
                return `(IProveTuple${N} ${a.params.map(s).join(" ")})`;
            }
            
            case "ArrayLiteral": {
                let units = a.elems.map((e) => 
                    (`(seq.unit ${s(e)})`));
                return `(seq.++ ${units.join(" ")})`
                
            }
        }
    }



    ast2smtlib(a: ASTNode | undefined) : string {
        if(a === undefined) return "NULL"
        var ancillae: string[] = []
        let renderedNode: string = this.renderNode(a)
        let mapped = (ancillae.length)
            ? `${ancillae.join("\n")}\n`
            : "";
        return `${mapped}${renderedNode}`
    }
}

export const LI = new LogicInterface();
export const ASTSMTLIB2: (line: Line | undefined) => string = LI.ast2smtlib;
