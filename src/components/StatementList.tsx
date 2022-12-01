import { AddIcon } from "@chakra-ui/icons";
import { Box, IconButton, Text } from "@chakra-ui/react";
import { StatementListCallbacks } from "../callbacks/statementListCallbacks";
import { StatementType } from "../types/Statement";
import Statement from "./Statement";

export type StatementListPropsType = {
  title: string;
  statements: StatementType[];
  callbacks: Pick<StatementListCallbacks, "add" | "update" | "remove">;
  isCollapsed?: boolean;
  isScrollable?: boolean
  indexToDisplayedIndex?: (index: number) => number;
  afterStatementEdit?: (index: number) => void;
}

export default function StatementList({ title, statements, callbacks, isCollapsed = false, isScrollable = false, indexToDisplayedIndex = x => x, afterStatementEdit = () => {} }: StatementListPropsType) {

  const makeStatementProps = (index: number) => ({
    statement: statements[index],
    index: indexToDisplayedIndex(index),
    onChange: (e: any) => callbacks.update(index, e.target.value),
    addAbove: () => callbacks.add(index),
    addBelow: () => callbacks.add(index + 1),
    deleteStatement: () => callbacks.remove(index),
    afterEdit: () => afterStatementEdit(index),
  });

  return <div style={{ display: 'flex', flexDirection: 'column' }}>
    <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'space-between', marginTop: '5px' }}>
      <Text>{title}</Text>
      <IconButton
        variant='outline'
        aria-label='Add row'
        size='xs'
        onClick={() => { callbacks.add() }}
        icon={<AddIcon />}
      />
    </div>
    {
      isCollapsed ?
        <>
          <Statement
            proofNode={true}
            {...makeStatementProps(0)}
          />
          <Text as='b'>. . .</Text>
          <Statement
            proofNode={true}
            {...makeStatementProps(statements.length - 1)}
          />
        </> :
        isScrollable ? <Box overflowY="scroll" maxHeight="10em">
         {statements.map((_s: StatementType, index: number) =>
          <Statement
            proofNode={true}
            {...makeStatementProps(index)}
            key={index}
          />)}
        </Box> : statements.map((_s: StatementType, index: number) =>
          <Statement
            proofNode={true}
            {...makeStatementProps(index)}
            key={index}
          />)
    }
  </div>
}
