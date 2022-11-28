import * as AST from "../types/AST";
import { FunctionData, PatternData } from "../types/LogicInterface";
import { fnSMT } from "./util";

export class LogicInterface {
    // persist after reset
    globals: Map<number, AST.ASTNode> = new Map();
    rendered_globals: Map<number, string> = new Map();
    rendered_tuples: Map<number, string> = new Map();
    functions: Map<string, FunctionData> = new Map();
    insID: number = 0;


    // change on reset
    givens: AST.ASTNode[] = [];
    goal: AST.ASTNode | undefined;
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
    addGlobal(n: AST.ASTNode): number | undefined {
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
    addGiven(n: AST.ASTNode): boolean {
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
    setGoal(n: AST.Term): AST.ASTNode | undefined {
        let old = this.goal;
        this.goal = n;
        return old
    }

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


    renderPattern(a: AST.Pattern, name: string): PatternData {
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

        let pdatas: [PatternData, AST.Term][] = [];
        for (let [i, a] of A.defs) {
            if (a.params.length != nparams) return undefined;

            let idx: number = 0;
            for (let p of a.params) {
                pdatas.push([
                    this.renderPattern(p, `IProveParameter${idx}`),
                    (a.def as AST.Term)
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

    addFnDecl(a: AST.FunctionDeclaration): AST.FunctionDeclaration | undefined {
        this.newFunction(a.symbol);
        let A = this.functions.get(a.symbol);
        if (!A) return undefined; // error case for typechecking

        let old = A.decl;
        A.decl = a;
        return old;
    }

    // Adds a function definition and returns its id within the definition of
    // this particular function
    addFnDef(a: AST.FunctionDefinition): number {
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

    renderNode(a: AST.ASTNode | undefined): string {
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
    ast2smtlib(a: AST.ASTNode | undefined) : string {
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

export const LI = new LogicInterface();
export const ASTSMTLIB2: (line: AST.Line | undefined) => string = LI.ast2smtlib;
