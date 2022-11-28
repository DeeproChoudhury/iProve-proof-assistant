import { StatefulTransformer } from "../types/LogicInterface";
import * as AST from "../types/AST";

// Given a function f: Term -> Term, returns a function which, given an AST A,
// returns the AST corresponding to a recursive application of f to the terms
// of A.
export function map_terms<T>(f: StatefulTransformer<AST.Term, T>, init: T, lazy: boolean = false): (A: AST.Term) => [AST.Term, T] {
    var R: StatefulTransformer<AST.ASTNode, T>
    var RT: (A: AST.Term, st: T, seen?: boolean) => [AST.Term, T]
    var RG: StatefulTransformer<AST.Guard, T>
    var RGT: StatefulTransformer<AST.Guard | AST.Term, T>
    var RT_ = (t: AST.Term | undefined, st: T): [AST.Term | undefined, T] =>
        (t ? RT(t, st, false) : [undefined, st]);
    var RG_ = (t: AST.Guard | undefined, st: T): [AST.Guard | undefined, T] =>
        (t ? RG(t, st) : [undefined, st]);

    
    R = (A: AST.ASTNode, st: T): [AST.ASTNode, T] => {
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

    RG = (A: AST.Guard, st_0: T): [AST.Guard, T] => {
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

    RGT = (A: AST.Guard | AST.Term, st: T): [AST.Guard | AST.Term, T] => {
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