import { Box, Radio, RadioGroup } from '@chakra-ui/react';
import { display } from "../parser/AST";
import { StatementType } from '../types/Statement';

export type ModalStatementPropsType = {
  statement: StatementType;
  index: number;
  tag: string;
  setTag: (v: string) => void;
  isReasonDisabled?: boolean,
  isConclusionDisabled?: boolean,
}

const ModalStatement = (props: ModalStatementPropsType) => {
  const {statement, index, tag, setTag, isReasonDisabled = false, isConclusionDisabled = false} = props;
  if (!statement.parsed) {
    return <></>;
  }
  return (
    <Box borderRadius='md' bg='whiteAlpha.300' color='white' my='1'>
      <div style={{display: 'flex'}}>
        <div style={{margin: 'auto 5px'}}>({index + 1})</div>
        <div style={{flex: '1', margin: 'auto 0px'}}>{display(statement.parsed)}</div>
        <RadioGroup size='sm' onChange={setTag} value={tag}>
          <div style={{display: 'flex', flexDirection: 'column', marginRight: '10px'}}>
            <Radio value='0'>Not Selected</Radio>
            <Radio value='1' isDisabled={
              isReasonDisabled || 
              statement.parsed.kind === "EndScope" || 
              statement.parsed.kind === "BeginScope" || 
              statement.parsed.kind === "Assumption" ||
              statement.parsed.kind === "VariableDeclaration"
              }>Reason</Radio>
            <Radio value='2' isDisabled={
              isConclusionDisabled || 
              statement.parsed.kind === "EndScope"  || 
              statement.parsed.kind === "BeginScope" ||             
              statement.parsed.kind === "Assumption" ||
              statement.parsed.kind === "VariableDeclaration"
              }>Conclusion</Radio>
          </div>
        </RadioGroup>
      </div>
    </Box>
  )
}

export default ModalStatement;
