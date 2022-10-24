import { useRef } from "react";
import { display } from "./AST";
import { Statement } from "./TextUpdaterNode";

export type StatementInputProps = {
    index: number;
    statement: Statement;
    onChange: (evt: any, updated: number) => void;
}

function StatementInput({index, statement, onChange}: StatementInputProps) {
    const input = useRef<HTMLInputElement>(null);
    const value = statement.parsed && document.activeElement !== input.current ? display(statement.parsed) : statement.value;
    return <input ref={input} onChange={e => onChange(e, index)} style={{ marginTop: '5px' }} key={index} value={value} />
}

export default StatementInput
