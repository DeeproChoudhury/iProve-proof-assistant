import { StatementType } from "./TextUpdaterNode";
import { Box, Radio, RadioGroup, Stack } from '@chakra-ui/react'
import { useState } from "react";

export type ModalStatementPropsType = {
  statement: StatementType;
  index: number;
  tag: string;
  setTag: (v: string) => void;
}

const ModalStatement = (props: ModalStatementPropsType) => {
  const {statement, index, tag, setTag} = props;
  return (
    <Box borderRadius='md' bg='whiteAlpha.300' color='white' my='1'>
      <div style={{display: 'flex'}}>
        <div style={{margin: 'auto 5px'}}>({index + 1})</div>
        <div style={{flex: '1'}}>{statement.value}</div>
        <RadioGroup size='sm' onChange={setTag} value={tag}>
          <div style={{display: 'flex', flexDirection: 'column', marginRight: '10px'}}>
            <Radio value='0'>Not Selected</Radio>
            <Radio value='1'>Reason</Radio>
            <Radio value='2'>Conclusion</Radio>
          </div>
        </RadioGroup>
      </div>
    </Box>
  )
}

export default ModalStatement;
