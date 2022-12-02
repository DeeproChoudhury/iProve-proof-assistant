import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { mutual_rec_on, rec_on } from "../logic/induction";
import { unifies } from "../logic/unifier";
import Z3Solver from "../logic/Solver";
import { ASTNode, Line, QuantifierApplication, Term, Type, TypeDef, Variable, VariableBinding } from "../types/AST";
import { AnyNodeType, InductionNodeData, InductionNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { getOutputs, isInductionNode, setNodeWithId, setStatementsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { unwrap_statements, updateWithParsed } from "../util/statements";
import { conjunct, display, imply, isTerm, range_over } from "../util/trees";
import { makeStatementListCallbacks } from "./statementListCallbacks";
import { IProveError } from "../types/ErrorLocation";
import { LI } from "../logic/LogicInterface";
import { makeSharedNodeCallbacks } from "./sharedNodeCallbacks";

export type InductionNodeCallbacks = InductionNodeData["thisNode"];

export const makeInductionNodeCallbacks = (
  nodesRef: MutableRefObject<AnyNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setNodes: Setter<AnyNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<IProveError | undefined>,
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


    let types: Line[] = unwrap_statements(node.data.types)
    //   :/
    if (types.some(x => x.kind != "TypeDef")) return;
    let tdefs: TypeDef[] = (types as TypeDef[])

    let motives_: Line[] = unwrap_statements(node.data.motive)
    if (motives_.some(x => x.kind != "QuantifierApplication" || !x.vars.length))
      return;
    let motives: QuantifierApplication[] = motives_ as QuantifierApplication[]
    let vbinds: VariableBinding[] = motives.map(m => m.vars[0])
    let identifiers: Variable[] = vbinds.map(v => v.symbol)
    let tidents_: (Type | undefined)[] = vbinds.map(v => v.type)
    if (tidents_.some(t => !t)) return;
    let tidents: Type[] = tidents_ as Type[]

    console.log("PREM", motives)
    let final_motives = motives.map((m): Term =>
      (m.vars.length < 2)
        ? m.term
        : {
          kind: "QuantifierApplication",
          term: m.term,
          vars: m.vars.slice(1),
          quantifier: m.quantifier
        }
    )

    console.log("RAW CASES", node.data.baseCases, node.data.inductiveCases)
    let cases: Line[] = unwrap_statements(node.data.baseCases.concat(node.data.inductiveCases))
    for (let c of cases) {
      console.log("HERE C", c)
      if (!isTerm(c)) {
        setError({
          kind: "Semantic",
          msg: "Inductive terms must be first-order formulae!"
        });
        setNode(node => ({...node, data: {...node.data, internalsStatus: "invalid"}}));
        return;
      }
    }

    let precond: Term | undefined = conjunct(cases as Term[])
    let cum_motives = conjunct(final_motives)
    console.log("CMOTIVE", cum_motives, final_motives)
    if (!cum_motives) {
      setError({
        kind: "Semantic",
        msg: "Inductive terms must be first-order formulae!"
      });
      setNode(node => ({...node, data: {...node.data, internalsStatus: "invalid"}}));
      return;
    }

    let tidentifiers = identifiers.map(
      (v, i): [Variable, Type] => [v, tidents[i] as Type])
    let IP: Term = (precond)
      ? imply(precond, range_over(cum_motives, tidentifiers))
      : range_over(cum_motives, tidentifiers)

    let gt_IP: Term = mutual_rec_on(tidents, tdefs)(identifiers.map(x=>x.ident), final_motives)
    
    console.log("GT", display(gt_IP))
    console.log("USER", display(IP))
    let verdict = unifies(IP, gt_IP)
    if (!verdict) {
      setError(undefined)
      setNode(node => ({...node, data: {...node.data, internalsStatus: "invalid"}}));
      return;
    }

    console.log("VERDICT", display(verdict.term))
    setNode(node => ({...node, data: {...node.data, internalsStatus: "valid"}}));
  };
  const checkEdges = async () => {
    const currEdges = edgesRef.current;
    const currNodes = nodesRef.current;
    const node = currNodes.find((n) => n.id === nodeId);
    if (!node || !isInductionNode(node)) return;

    const incomingEdges = currEdges.filter((e) => e.target === nodeId);
    const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
    const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
    const givens = incomingNodes.flatMap(getOutputs);
    const expImplications = [...node.data.baseCases, ...node.data.inductiveCases];
    if (declarationsRef.current.some(s => !s.parsed) || expImplications.some(s => !s.parsed)) {
      return; // TODO: show error message here
    }
    {/* BEGIN LOGIC INTERFACE CRITICAL REGION */}
    let success: boolean = false;

    // TODO: WIRE UP TYPES BOX?
    LI.setDeclarations(unwrap_statements(node.data.declarationsRef.current))

    let goal: Term | undefined = conjunct(unwrap_statements(expImplications))
    if (goal) { 
      const verdict = await LI.entails(unwrap_statements(givens), goal)
      success = (verdict.kind === "Valid")
    }
    console.log('passed this?')
    
    {/* END LOGIC INTERFACE CRITICAL REGION */}

    setNode((node) => {
      //set nodes
      return {
        ...node,
        data: {
          ...node.data,
          edgesValid: success ? "valid" : "invalid"
        }
      };
    });
    setEdges(eds => {
      //set edges
      return eds.map((edge) => {
        if (edge.target === nodeId) {
          edge.type = success ? "checked" : "invalid";
        }
        return edge;
      });
    });
    return;
  };
  return {
    ...makeSharedNodeCallbacks(setNodes, isInductionNode, nodeId),
    ...statementLists,
    parseAll,
    checkInternal,
    checkEdges,
    invalidateInternals: () => setNode(node => ({...node, data: {...node.data, internalsStatus: "unchecked"}}))
  };
};
