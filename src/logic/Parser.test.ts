import evaluate from "./Parser"
const util = require("util")
const D = (x) => {
  console.log(util.inspect(x, false, null, true))
}

test('Supervillain proof', () => {
  expect(evaluate("FA x.[person(x) & FA y.[childof(y,x) -> rich(y)] -> happy(x)]").kind)
    .toBe("QuantifierApplication");
  expect(evaluate("FA x.[EX y.[childof(x,y) & supervillain(y)] -> supervillain(x)]").kind)
    .toBe("QuantifierApplication");
  expect(evaluate("FA x.[supervillain(x) -> rich(x)]").kind)
    .toBe("QuantifierApplication");
  expect(evaluate("FA x.[supervillain(x) -> person(x)]").kind)
    .toBe("QuantifierApplication");

  expect(evaluate("var Gru").kind)
    .toBe("VariableDeclaration");
  expect(evaluate("supervillain(Gru)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("person(Gru)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("var Agnes").kind)
    .toBe("VariableDeclaration");
  expect(evaluate("childof(Agnes, Gru)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("childof(Agnes, Gru) & supervillain(Gru)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("EX y.[childof(Agnes, y) & supervillain(y)]").kind)
    .toBe("QuantifierApplication");
  expect(evaluate("supervillain(Agnes)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("rich(Agnes)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("childof(Agnes, Gru) -> rich(Agnes)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("FA y.[childof(y, Gru) -> rich(y)]").kind)
    .toBe("QuantifierApplication");
  expect(evaluate("person(Gru) & FA y.[childof(y, Gru) -> rich(y)]").kind)
    .toBe("FunctionApplication");
  expect(evaluate("supervillain(Gru) -> happy(Gru)").kind)
    .toBe("FunctionApplication");
  expect(evaluate("FA x.[supervillain(x) -> happy(x)]").kind)
    .toBe("QuantifierApplication");
});
