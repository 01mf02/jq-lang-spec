jq BNF:

```
defs = module def*
main = module term

module = "module" term ";" (("include" cstr | "import" cstr "as" var) ";")*

term(op) = atom (op atom)* (("as" var)? "|" term(op))?

term          = term(bin_op | "and" | "or" | ",")
term_no_comma = term(bin_op | "and" | "or"      )

atom = atom_head "?"? path

atom_head =
  | num
  | str
  | def term
  | "-" atom
  | "if" term "then" term ("elif" term "then" term)* ("else" term)? "end"
  | "try" atom ("catch" atom)?
  | "label" var "|" term
  | "break" var
  | fold atom "as" var args
  | var
  | const args?
  | "[" term? "]"
  | "{" (obj_entry ("," obj_entry)* ","?)? "}"
  | "." key_opt? path
  | ".."
  | "(" term ")"

def = "def" const args? ":" term ";"

fold = "reduce" | "foreach"
args = "(" term ("," term)* ")"
num =
str = @const? cstr
cstr =
bin_op =
const =
var =

obj_entry =
  | "(" term        ")" ":" term_no_comma
  |  (var | key | str) (":" term_no_comma)?

path = path_part_opt* ("." key_opt path_part_opt*)*
path_part_opt = "[" path_part "]" "?"?
key_opt = key "?"?
path_part = term | term ":" term | term ":" | ":" term
```

We will now create a bridge between the concrete jq syntax and the
high-level intermediate representation.
In particular, we will simplify the following constructions of the jq syntax:

- Shadowed definitions:
  We can define a filter with the same name and arity multiple times; for example,
  if we define `def one: 1; def two: one + one; def one: [1]`,
  then `two` will yield `2` and `one` will yield `[1]`.
  We can always rename definitions to eliminate such shadowing; e.g. by
  `def one: 1; def two: one + one; def one_: [1]`.
- Definitions with variable bindings:
  The jq language allows for definitions of the shape
  `def x(a_1; ...; a_n): g`, where for any `i`, `a_i` may be either
  an identifier (without a leading `$`) or
  a variable (with leading `$`).
  We can always transform definitions to a semantically equivalent form where
  all arguments are non-variables by the following procedure:
  We repeat the following as long as there is a largest `i` such that `a_i` is a variable:
  We come up with a fresh identifier `b_i`,
  replace `g` by `b_i as a_i | g`, and
  replace the argument `a_i` by `b_i`.
  For example, this could replace
  `def f($x; g): $x + g` by
  `def f( x; g): x as $x | $x + g`.
- Nested definitions:
  We can nest filter definitions.
  This is more than just syntactic sugar to limit the scope of an auxiliary filter;
  for example, consider the definition `def repeat(f): f, repeat(f)`,
  which repeats the output of the filter `f` ad infinitem.
  Most jq implementations to date take quadratic time to evaluate $n$ outputs of `repeat(0)`,
  because every time that `repeat(f)` calls `repeat(f)`,
  it creates a new closure around `f` to yield the `f` for the recursive call.^[
    In principle, such calls could be detected and optimized.
    For example, in Haskell, we can express `repeat` by
    `f x = x () : f (\ () -> x ())` and see that
    `f (\ () -> 0)` executes in linear time.
    However, when we change the definition of `f` to
    `f x = x () : f (\ () -> 1 + x ())` (adding 1 to every call of `x ()`), then
    `f (\ () -> 0)` executes in quadratic time.
    This is because when the $n$-th recursive call of `f` calls `x()`, it evaluates to
    `1 + ... + 1 + 0`, where this sum consists of $n$ summands.
  ]
  However, nested definitions allow the same filter to be written as
  `def repeat(f): def rec: f, rec; rec`.
  This makes it clear that `f` remains the same for all recursive calls,
  and allows evaluation of $n$ outputs of `repeat(0)` in linear time.
  For the sake of this specification, however,
  we assume that no nested definitions are present.
  We can always extract a nested definition from its parent definition by
  adding all arguments from ancestor definitions to its arguments.
  For our improved `repeat` example, this would yield
  `def repeat_rec(f): f, repeat_rec(f); def repeat(f): repeat_rec(f)`.
- Conditional expressions with multiple branches:
  if-then-else expressions have the shape
  - `if c then t`, followed by arbitrarily many instances of
  - `elif c then t`, potentially followed by
  - `else e`, and terminated by
  - `end`.
  Here, `c`, `t`, and `e` denote expressions.
  For example:

  ```
  if c_0 then t_0 elif c_1 then t_1 ... elif c_n then t_n else e end
  ```
  We write such an expression equivalently as:
  ```
  if c_0 then t_0 else if c_1 then t_1 ... else if c_n then t_n else e end ... end end
  ```
  When `else e` is not given, then we assume that `else .` was given.
  Finally, in HIR, we omit the trailing `end`.
