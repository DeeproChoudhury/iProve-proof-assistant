import { MutableRefObject } from "react";
import { Edge } from "reactflow";
import { rec_on } from "../logic/induction";
import { unifies } from "../logic/unifier";
import Z3Solver from "../logic/Solver";
import { Line, Term, Type, TypeDef, Variable, VariableBinding } from "../types/AST";
import { ErrorLocation } from "../types/ErrorLocation";
import { InductionNodeType, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { setNodeWithId, setStatementsForNode } from "../util/nodes";
import { Setter } from "../util/setters";
import { unwrap_statements, updateWithParsed } from "../util/statements";
import { conjunct, display, imply, isTerm, range_over } from "../util/trees";
import { makeStatementListCallbacks } from "./statementListCallbacks";
import { LI } from "../logic/LogicInterface";


export const makeInductionNodeCallbacks = (
  nodesRef: MutableRefObject<StatementNodeType[]>,
  inductionNodesRef: MutableRefObject<InductionNodeType[]>,
  edgesRef: MutableRefObject<Edge[]>,
  declarationsRef: MutableRefObject<StatementType[]>,
  setInductionNodes: Setter<InductionNodeType[]>,
  setEdges: Setter<Edge[]>,
  setError: Setter<ErrorLocation | undefined>,
  z3: Z3Solver.Z3Prover
) => (
  nodeId: string
) => {
  const setNode = setNodeWithId(setInductionNodes, nodeId);
  return {
    delete: (): void => setInductionNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    types: makeStatementListCallbacks(setStatementsForNode(setNode, "types")),
    motive: makeStatementListCallbacks(setStatementsForNode(setNode, "motive")),
    baseCases: makeStatementListCallbacks(setStatementsForNode(setNode, "baseCases")),
    inductiveCases: makeStatementListCallbacks(setStatementsForNode(setNode, "inductiveCases")),
    checkSyntax: (): void => setNode(node => {
      setError(undefined);

      return {
        ...node,
        data: {
          ...node.data,
          types: node.data.types.map(updateWithParsed(setError)),
          motive: node.data.motive.map(updateWithParsed(setError)),
          baseCases: node.data.baseCases.map(updateWithParsed(setError)),
          inductiveCases: node.data.inductiveCases.map(updateWithParsed(setError))
        }
      };
    }),
    checkEdges: async () => {
      const currEdges = edgesRef.current;
      const currNodes = nodesRef.current;
      const currInductionNodes = inductionNodesRef.current;
      const node = currInductionNodes.find((n) => n.id === nodeId);
      if (!node) return true;
      const incomingEdges = currEdges.filter((e) => e.target === nodeId);
      const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
      const incomingNodes = currNodes.filter(node => incomingNodesIds.has(node.id))
      const incomingInductionNodes = currInductionNodes.filter(node => incomingNodesIds.has(node.id));
      const inductionGivens = incomingInductionNodes.map(node => node.data.motive[0]);
      const givens = [...incomingNodes.flatMap(node => node.data.goals), ...inductionGivens];
      const expImplications = [...node.data.baseCases, ...node.data.inductiveCases];
      if (declarationsRef.current.some(s => !s.parsed) || expImplications.some(s => !s.parsed)) {
        return false; // TODO: show error message here
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
            correctImplication: success ? "valid" : "invalid"
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
      return success;
    },
    checkPrinciple: async () => {
      const node = inductionNodesRef.current.find((n) => n.id === nodeId);
      if (!node) return;

      node.data.thisNode.checkSyntax();

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
        return;
      }

      console.log("VERDICT", display(verdict.term))
    }
  };
};

export type InductionNodeCallbacks = ReturnType<ReturnType<typeof makeInductionNodeCallbacks>>;
