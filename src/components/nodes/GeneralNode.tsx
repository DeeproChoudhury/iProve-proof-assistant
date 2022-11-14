import { ReactElement } from "react";
import { GeneralNodeData, InductionData, NodeData } from "../../types/Node";
import InductionNode from "./InductionNode";
import TextUpdaterNode from "./TextUpdaterNode";

/*  */
export default function GeneralNode( { data } : { data : GeneralNodeData } ) : ReactElement {
    if (data.type === "induction") {
        // data = data as InductionData;
        const nodeData : InductionData = data as InductionData;
        return InductionNode({ data : nodeData });
    } else {
        const nodeData : NodeData = data as NodeData;
        return TextUpdaterNode({ data : nodeData });
    }
}