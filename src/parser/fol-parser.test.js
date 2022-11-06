import evaluate from "./fol-parser"

test('Supervillain proof', () => {
  evaluate("FA x.[person(x) & FA y.[childof(y,x) -> rich(y)] -> happy(x)]");
  evaluate("FA x.[EX y.[childof(x,y) & supervillain(y)] -> supervillain(x)]");
  evaluate("FA x.[supervillain(x) -> rich(x)]");
  evaluate("FA x.[supervillain(x) -> person(x)]");
  evaluate("var Gru");
  evaluate("supervillain(Gru)");
  evaluate("person(Gru)");
  evaluate("var Agnes");
  evaluate("childof(Agnes, Gru)");
  evaluate("childof(Agnes, Gru) & supervillain(Gru)");
  evaluate("EX y.[childof(Agnes, y) & supervillain(y)]");
  evaluate("supervillain(Agnes)");
  evaluate("rich(Agnes)");
  evaluate("childof(Agnes, Gru) -> rich(Agnes)");
  evaluate("FA y.[childof(y, Gru) -> rich(y)]");
  evaluate("person(Gru) & FA y.[childof(y, Gru) -> rich(y)]");
  evaluate("supervillain(Gru) -> happy(Gru)")
  evaluate("FA x.[supervillain(x) -> happy(x)]")
});