import { Box, Radio, RadioGroup } from '@chakra-ui/react';
import { StatementType } from '../types/Statement';
import { display } from '../util/trees';

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
    <Box borderRadius='md' bg='blackAlpha.100' color='black' my='1'>
      <div style={{display: 'flex'}}>
        <div style={{margin: 'auto 5px'}}>({index + 1})</div>
        <div style={{flex: '1', margin: 'auto 0px'}}>{display(statement.parsed)}</div>
        <RadioGroup colorScheme="purple" size='sm' onChange={setTag} value={tag}>
          <div style={{display: 'flex', flexDirection: 'column', marginRight: '10px'}}>
            <Radio borderColor="gray" value='0'>Not Selected</Radio>
            <Radio borderColor="gray" value='1' isDisabled={
              isReasonDisabled || 
              statement.parsed.kind === "EndScope" || 
              statement.parsed.kind === "BeginScope" || 
              statement.parsed.kind === "Assumption" ||
              statement.parsed.kind === "Skolemize" ||
              statement.parsed.kind === "VariableDeclaration"
              }>Reason</Radio>
            <Radio borderColor="gray" value='2' isDisabled={
              isConclusionDisabled || 
              statement.parsed.kind === "EndScope"  || 
              statement.parsed.kind === "BeginScope" ||             
              statement.parsed.kind === "Assumption" ||
              statement.parsed.kind === "Skolemize" ||
              statement.parsed.kind === "VariableDeclaration"
              }>Conclusion</Radio>
          </div>
        </RadioGroup>
      </div>
    </Box>
  )
}

export default ModalStatement;
