import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { rec_on } from "../logic/induction";
import { unifies } from "../logic/unifier";
import Z3Solver from "../logic/Solver";
import { Line, Term, Type, TypeDef, Variable, VariableBinding } from "../types/AST";
import { ErrorLocation } from "../types/ErrorLocation";
import { AnyNodeType, InductionNodeData, InductionNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { isInductionNode, setNodeWithId, setStatementsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { updateWithParsed } from "../util/statements";
import { conjunct, display, imply, isTerm, range_over } from "../util/trees";
import { makeStatementListCallbacks } from "./statementListCallbacks";

export type InductionNodeCallbacks = InductionNodeData["thisNode"];

export const makeInductionNodeCallbacks = (
  nodesRef: MutableRefObject<AnyNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setNodes: Setter<AnyNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
): InductionNodeCallbacks => {
  const setNode = setNodeWithId(setNodes, isInductionNode, nodeId);
  const statementLists = {
    types: makeStatementListCallbacks(setStatementsForNode(setNode, "types"), setError),
    motive: makeStatementListCallbacks(setStatementsForNode(setNode, "motive"), setError),
    baseCases: makeStatementListCallbacks(setStatementsForNode(setNode, "baseCases"), setError),
    inductiveCases: makeStatementListCallbacks(setStatementsForNode(setNode, "inductiveCases"), setError)
  }
  const parseAll = (): void => {
    setError(undefined);
    statementLists.types.parseAll();
    statementLists.motive.parseAll();
    statementLists.baseCases.parseAll();
    statementLists.inductiveCases.parseAll();
    setNode(node => {
      return {
        ...node,
        data: {
          ...node.data,
          allParsed: [
            node.data.types,
            node.data.motive,
            node.data.baseCases,
            node.data.inductiveCases
          ].every(list => list.every(statement => statement.parsed))
        }
      }    
    });
  };
  const checkInternal = async () => {
    const node = nodesRef.current.find((n) => n.id === nodeId);
    if (!node || node.type !== "inductionNode") return;

    setNode(node => ({...node, data: {...node.data, internalsStatus: "checking"}}));
    node.data.thisNode.parseAll();

    let type_: StatementType | undefined = node.data.types[0]
    if (!type_ || !type_.parsed) return;
    let type: Line = type_.parsed
    if (type.kind != "TypeDef") return;
    let tdef: TypeDef = type

    let motive_: StatementType | undefined = node.data.motive[0]
    if (!motive_ || !motive_.parsed) return;
    let motive: Line = motive_.parsed
    if (motive.kind != "QuantifierApplication" || motive.vars.length != 1) 
      return;
    let vbind: VariableBinding = motive.vars[0];
    let identifier: Variable = vbind.symbol
    let tident: Type | undefined = vbind.type
    if (!tident) return;
    motive = motive.term

    let cases: Line[] = 
      node.data.baseCases
        .concat(node.data.inductiveCases)
        .map(x => x.parsed)
        .filter(x => x != undefined)
        .map(x => x as Line);

    for (let c of cases) {
      if (!isTerm(c)) {
        setError(undefined);
        setNode(node => ({...node, data: {...node.data, internalsStatus: "invalid"}}));
        return;
      }
    }

    let precond: Term | undefined = conjunct(cases as Term[])
    let IP: Term = (precond)
      ? imply(precond, range_over(motive, [[identifier, tident]]))
      : range_over(motive, [[identifier, tident]])

    let gt_IP: Term = rec_on(tident, tdef)(identifier.ident, motive)
    console.log("GT", display(gt_IP))
    console.log("USER", display(IP))
    let verdict = unifies(IP, gt_IP)
    if (!verdict) {
      setError(undefined)
      setNode(node => ({...node, data: {...node.data, internalsValid: "invalid"}}));
      return;
    }

    console.log("VERDICT", display(verdict.term))
    setNode(node => ({...node, data: {...node.data, internalsValid: "valid"}}));
  };
  const checkEdges = () => { throw "unimplemented" };
  return {
    delete: (): void => setNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    ...statementLists,
    parseAll,
    checkInternal,
    checkEdges
  };
};
