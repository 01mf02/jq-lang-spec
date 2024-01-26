#import "@preview/ctheorems:1.1.0": thmplain, thmrules
#import "article.typ": article
#show: thmrules

#show: doc => article(
  title: [A formal specification of the jq language],
  authors: (
    (
      name: "Michael Färber",
      email: "michael.faerber@gedenkt.at",
    ),
  ),
  abstract: [
    jq is a widely used tool that provides a programming language to manipulate JSON data.
    However, it is currently only specified by its implementation,
    making it difficult to reason about its behaviour.
    To this end, I provide a syntax and denotational semantics for
    a subset of the jq language.
    In particular, the semantics provide a new way to interpret updates.
  ],
  doc,
)

#set heading(numbering: "1.")
#set raw(lang: "jq")

#let thm(x, y, ..args) = thmplain(x, y, inset: (left: 0em, right: 0em), args)
#let example = thm("example", "Example")
#let lemma = thm("theorem", "Lemma")
#let proof = thm("proof", "Proof",
  bodyfmt: body => [
    #body #h(1fr) $square$    // Insert QED symbol
  ]
).with(numbering: none)

#let circ = [#box($circle.small$)]
#let update = $models$
#let var(x) = $\$#x$
#let circeq = [#box($circ#h(0pt)=$)]

= TODO:

- fix QED at end of proof
- fix substitution syntax
- extend to full JSON
- constant filter (string, number)
- lowering goes from HIR to MIR:
  - $.[p_1]dots[p_n]$
  - $f circ g$
  - $f circeq g$
  - $f = g$
  - $f?$
  - if-then-else
- convention: error $e$, result $r$, value $v$, path part $p$, variable $var(x)$
- error: value or break
- specify $.[l:h]$ and $"try" f "catch" g$, $"label" var(x) | g$, $"break" var(x)$
- specify arithmetic operations for non-numeric values (recursive object merge, ...)
- try/catch difference: allow simulation via $"label" var(x) | "try" f "catch" (g, "break" var(x))$
- why is empty not definable? because of updates!
- define inputs, keys
- is $.[var(x)]?$ equivalent to $(.[var(x)])?$?
- is $"foreach" x "as" var(x) (y_0; f)$ equivalent to $"foreach" x "as" var(x) (y_0; "first"(f))$ in the jq implementation?
- define foreach via for and clarify that latter is not part of jq
- define $"dom"(v)$
- xs -> $x$
- literature research

Lowering paths:

$f[p_1]dots[p_n] equiv . "as" var(x') | f | .[p_1]_var(x') | dots | .[p_n]_var(x')$

#figure(table(columns: 2, align: (left, right),
  $[p]$, $.[p]_var(x)$,
  $[ ]$, $.[]$,
  $[f]$, $(var(x) | f) "as" var(y') | .[var(y')]$,
  $[f:]$, $(var(x) | f) "as" var(y') | .[var(y') :]$,
  $[:g]$, $(var(x) | g) "as" var(z') | .[: var(z')]$,
  $[f:g]$, $(var(x) | f) "as" var(y') | (var(x) | g) "as" var(z') | .[var(y') : var(z')]$,
))



= Introduction

UNIX has popularised the concept of _filters_ and _pipes_ #cite(label("DBLP:journals/bstj/Ritchie84")):
A filter is a program that reads from an input stream and writes to an output stream.
Pipes are used to compose filters.

JSON (JavaScript Object Notation) is a widely used data serialisation format @rfc8259.
A JSON value is either
null,
a boolean,
a number,
a string,
an array of values, or
an associative map from strings to values.

jq is a tool that provides a language to define filters and an interpreter to execute them.
Where UNIX filters operate on streams of characters,
jq filters operate on streams of JSON values.
This allows to manipulate JSON data with relatively compact filters.
For example, given as input the public JSON dataset of streets in Paris @paris-voies,
jq retrieves
the number of streets (6508) with the filter "`length`",
the names of the streets with the filter "`.[].fields.nomvoie`", and
the total length of all streets (1576813 m) with the filter "`[.[].fields.longueur] | add`".
jq provides a Turing-complete language that is interesting on its own; for example,
"`[0, 1] | recurse([.[1], add])[0]"` generates the stream of Fibonacci numbers.
This makes jq a widely used tool.
I refer to the program jq as "jq" and to its language as "the jq language".

The semantics of the jq language are only
informally specified in the jq manual @jq-manual.
However, the documentation frequently does not cover certain cases,
or the implementation downright contradicts the documentation.
For example, the documentation states that the filter `limit(n; f)`
"extracts up to `n` outputs from `f`".
However, `limit(0; f)` extracts up to 1 outputs from `f`, and
for negative values of `n`, `limit(n; f)` extracts all outputs of `f`.
While this particular example could easily be corrected,
the underlying issue of having no formally specified semantics to rely on remains.
Having such semantics also allows to determine whether
certain behaviour of the implementation is accidental or intended.

However, a formal specification of the behaviour of jq would be very verbose,
because jq has many special cases whose merit is not apparent.
Therefore, I have striven to create
denotational semantics (@semantics) that closely resemble those of jq such that
in most cases, their behaviour coincides, whereas they may differ in more exotic cases.
One particular improvement over jq are the new update semantics (@updates), which
are simpler to describe and implement,
eliminate a range a potential errors, and
allow for more performant execution.


= Preliminaries <preliminaries>

This goal of this section is to convey an intuition about how jq functions.
The official documentation of jq is @jq-manual.

jq programs are called _filters_.
For now, let us consider a filter to be a function from a value to a (lazy) stream of values.
Furthermore, let us assume a value to be either a boolean, an integer, or an array of values.

The identity filter "`.`" returns a stream containing the input.

Arithmetic operations, such as
addition, subtraction, multiplication, division, and remainder,
are available in jq.
For example, "`. + 1`" returns a stream containing the successor of the input.
Here, "`1`" is a filter that returns the value `1` for any input.

Concatenation is an important operator in jq:
The filter "`f, g`" concatenates the outputs of the filters `f` and `g`.
For example, the filter "`., .`" returns a stream containing the input value twice.

Composition is one of the most important operators in jq:
The filter "`f | g`" maps the filter `g` over all outputs of the filter `f`.
For example, "`(1, 2, 3) | (. + 1)`" returns `2, 3, 4`.

Arrays are created from a stream produced by `f` using the filter "`[f]`".
For example, the filter "`[1, 2, 3]`"
concatenates the output of the filters "`1`", "`2`", and "`3`" and puts it into an array,
yielding the value `[1, 2, 3]`.
The inverse filter "`.[]`" returns a stream containing the values of an array
if the input is an array.
For example, running "`.[]`" on the array `[1, 2, 3]` yields
the stream `1, 2, 3` consisting of three values.
We can combine the two shown filters to map over arrays;
for example, when given the input `[1, 2, 3]`,
the filter "`[.[] | (. + 1)]`" returns a single value `[2, 3, 4]`.
The values of an array at indices produced by `f` are returned by "`.[f]`".
For example, given the input `[1, 2, 3]`, the filter "`.[0, 2, 0]`"
returns the stream `1, 3, 1`.

Case distinctions can be performed with the filter "`if f then g else h end`".
For every value `v` produced by `f`, this filter
returns the output of `g` if `v` is true and the output of `h` otherwise.
For example, given the input `1`,
the filter "`if (. < 1, . == 1, . >= 1) then . else [] end`" returns `[], 1, 1`.

Fix points are calculated as follows:
Given a filter `f`, "`recurse(f)`" returns the output of "`., (f | recurse(f))`".
This way, we can define a filter to calculate the factorial function, for example.

#example("Factorial")[
  Let us define a filter `fac` that should return $n!$ for any input number $n$.
  We will define `fac` using the fix point of a filter `update`.
  The input and output of `update` shall be an array `[n, acc]`,
  satisfying the invariant that the final output is `acc` times the factorial of `n`.
  The initial value passed to `update` is the array "`[., 1]`".
  We can retrieve `n` from the array with "`.[0]`" and `acc` with "`.[1]`".
  We can now define `update` as "`if .[0] > 1 then [.[0] - 1, .[0] * .[1]] else empty end`",
  where "`empty`" is a filter that returns an empty stream.
  Given the input value `4`, the filter "`[., 1] | recurse(update)`" returns
  `[4, 1], [3, 4], [2, 12], [1, 24]`.
  We are, however, only interested in the accumulator contained in the last value.
  So we can write "`[., 1] | last(recurse(update)) | .[1]`", where
  "`last(f)`" is a filter that outputs the last output of `f`.
  This then yields a single value `24` as result.
] <ex:fac>


Composition can also be used to bind values to _variables_.
The filter "`f as $x | g`" performs the following:
Given an input value `i`,
for every output `o` of the filter `f` applied to `i`,
the filter binds the variable `$x` to the value `o`, making it accessible to `g`, and
yields the output of `g` applied to the original input value `i`.
For example, the filter "`(0, 2) as $x | ((1, 2) as $y | ($x + $y))`"
yields the stream `1, 2, 3, 4`.
Note that in this particular case, we could also write this as "`(0, 2) + (1, 2)`",
because arithmetic operators such as "`f + g`" take as inputs
the Cartesian product of the output of `f` and `g`.
#footnote[
  #set raw(lang: "haskell")
  Haskell users might appreciate the similarity of the two filters
  to their Haskell analoga
  "`[0, 2] >>= (\x -> [1, 2] >>= (\y -> return (x+y)))`" and
  "`(+) <$> [0, 2] <*> [1, 2]`", which both return
  `[1, 2, 3, 4]`.
]
However, there are cases where variables are indispensable.

#example("Variables Are Necessary")[
  jq defines a filter "`inside(xs)`" that expands to "`. as $x | xs | contains($x)`".
  Here, we wish to pass `xs` as input to `contains`, but at the same point,
  we also want to pass the input given to `inside` as an argument to `contains`.
  Without variables, we could not do both.
]

Folding over streams can be done using `reduce` and `foreach`:
The filter "`reduce xs as $x (init; f)`" keeps
a state that is initialised with the output of `init`.
For every element `$x` yielded by the filter `xs`,
`reduce` feeds the current state to the filter `f`, which may reference `$x`,
then sets the state to the output of `f`.
When all elements of `xs` have been yielded, `reduce` returns the current state.
For example, the filter "`reduce .[] as $x (0; . + $x)`"
calculates the sum over all elements of an array.
Similarly, "`reduce .[] as $x (0; . + 1)`" calculates the length of an array.
These two filters are called "`add`" and "`length`" in jq, and
they allow to calculate the average of an array by "`add / length`".
The filter "`foreach xs as $x (init; f)`" is similar to `reduce`,
but also yields all intermediate states, not only the last state.
For example, "`foreach .[] as $x (0; . + $x)`"
yields the cumulative sum over all array elements.

Updating values can be done with the operator "`|=`",
which has a similar function as lens setters in languages such as Haskell
#cite(label("DBLP:conf/popl/FosterGMPS05"))
#cite(label("DBLP:journals/programming/PickeringGW17")):
Intuitively, the filter "`p |= f`" considers any value `v` returned by `p` and
replaces it by the output of `f` applied to `v`.
We call a filter on the left-hand side of "`|=`" a _path expression_.
For example, when given the input `[1, 2, 3]`,
the filter  "`.[] |= (. + 1)`" yields `[2, 3, 4]`, and
the filter "`.[1] |= (. + 1)`" yields `[1, 3, 3]`.
We can also nest these filters;
for example, when given the input `[[1, 2], [3, 4]]`,
the filter "`(.[] | .[]) |= (. + 1)`" yields `[[2, 3], [4, 5]]`.
However, not every filter is a path expression; for example,
the filter "`1`" is not a path expression because
"`1`" does not point to any part of the input value
but creates a new value.

Identities such as
"`.[] |= f`" being equivalent to "`[.[] | f]`", or
"`. |= f`" being equivalent to `f`,
would allow defining the behaviour of updates.
However, these identities do not hold in jq due the way it
handles filters `f` that return multiple values.
In particular, when we pass `0` to the filter "`. |= (1, 2)`",
the output is `1`, not `(1, 2)` as we might have expected.
Similarly, when we pass `[1, 2]` to the filter "`.[] |= (., .)`",
the output is `[1, 2]`, not `[1, 1, 2, 2]` as expected.
This behaviour of jq is cumbersome to define and to reason about.
This motivates in part the definition of more simple and elegant semantics
that behave like jq in most typical use cases
but eliminate corner cases like the ones shown.


= Values & Errors

- JSON
- YAML
- numbers
- errors
- $"error"$
- multiplication
- subtraction
- division
- modulo
- equality

An object is a unordered map from strings to values.
We also refer to the domain of an object as _keys_.

By convention, we write
$v$ for values,
$n$ for numbers,
$s$ for strings,
$a$ for arrays,
$o$ for objects,
$c$ for characters,
$k$ for object keys, and
$e$ for errors.

The domain of a value is defined as follows:

$ "dom"(v) := cases(
  [0  , dots,   n] & "if " v = [v_0, dots, v_n],
  [k_0, dots, k_n] & "if " v = {k_0: v_0, dots, k_n: v_n},
  "error"          & "otherwise",
) $

We define the _length_ of a value as follows:

$ abs(v) := cases(
  0       & "if " v = "null",
  abs(n)  & "if " v "is a number" n,
  n       & "if " v = c_1...c_n,
  n       & "if " v = [v_1, dots, v_n],
  n       & "if " v = {k_1: v_1, dots, k_n: v_n},
  "error" & "otherwise (if " v in {"true", "false"}")",
) $

We define addition of two values as follows:

$ l + r := cases(
  v & "if" l = "null" "and" r = v", or" l = v "and" r = "null",
  n_1 + n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  c_(l,1)...c_(l,m)c_(r,1)...c_(r,n) & "if" l = c_(l,1)...c_(l,m) "and" r = c_(r,1)...c_(r,n),
  [l_1, ..., l_m, r_1, ..., r_n] & "if" l = [l_1, dots, l_m] "and" r = [r_1, dots, r_n],
  (union.big_(k in "dom"(l) without "dom"(r)) {k: l[k]}) union r & "if" l = {...} "and" r = {...},
  "error" & "otherwise",
) $

The most complicated case here is the addition of two objects:
It simply states that the addition is _right-biased_; i.e.,
if we have two objects $l$ and $r$, then $(l + r)[i] = r[i]$.

We will now introduce an indexing operator#footnote[
  While we will use this operator to define jq's `.[i]` operator,
  it does not capture the full complexity of `.[i]`; for example,
  `.[i]` is also defined for cases where `i` yields a negative number.
  We will address these differences later in @semantics.
]:

$ v[i] := cases(
  v_i    & "if" v = [v_0, dots, v_n] "," i in bb(N)", and" i <= n,
  "null" & "if" v = [v_0, dots, v_n] "," i in bb(N)", and" i > n,
  v_j    & "if" v = {k_0: v_0, dots, k_n: v_n}"," i "is a string, and" k_j = i,
  "null" & "if" v = {k_0: v_0, dots, k_n: v_n}"," i "is a string, and" i in.not {k_0, dots, k_n},
  "error" & "otherwise",
) $

The idea behind this indexing operator is as follows:
It returns $"null"$ if
the value $v$ does not contain a value at index $i$,
but $v$ could be _extended_ to contain one.
More formally, $v[i]$ is $"null"$ if $v eq.not "null"$ and
there exists some value $v' = v + delta$ such that $v'[i]$ is not null.

We establish a total order on values:
$ "null" < "false" < "true" < n < s < a < o, $ where
$n$ is a number,
$s$ is a string,
$a$ is an array, and
$o$ is an object.
We assume that there is a total order on numbers.
Arrays are compared lexicographically.
Two objects $o_1$ and $o_2$ are compared as follows:
For both objects $o_i$ ($i in {1, 2}$),
we sort the array $"dom"(o_i)$ to obtain the ordered array of keys
$k_i = [k_1, dots, k_n]$, from which we obtain
$v_i = [o[k_1], dots, o[k_n]]$.
If $k_1 = k_2$, the ordering of $o_1$ and $o_2$ is the ordering of $v_1$ and $v_2$,
otherwise, the ordering of $o_1$ and $o_2$ is the ordering of $k_1$ and $k_2$.

#example[
  TODO: For object comparison.
]

= Syntax

This section describes the syntax for a subset of the jq language
that will be used later to define the semantics in @semantics.
To set the formal syntax apart from
the concrete syntax introduced in @preliminaries,
we use cursive font (as in "$f$", "$v$") for the specification
instead of the previously used typewriter font (as in "`f`", "`v`").

A _filter_ $f$ is defined by
$ f := n | var(x) | . | .[] | .[f] | [f] | (f) | f? | f star f | f circ f | "if" f "then" f "else" f | x | x(f; dots; f) $
where $n$ is an integer and $x$ is an identifier (such as "empty").

By convention, we write $var(x')$ to denote a fresh variable.
The potential instances of $star$ and $circ$ are given in @tab:binops.
Furthermore, $f$ can be
a variable binding of the shape "$f "as" var(x) | f$" or
a fold of the shape "$phi med f "as" var(x) (f; f)$", where $phi$ is either "reduce" or "for".

#figure(
  table(
    columns: 3,
    [Name], [Symbol], [Operators],
    [Complex], $star$, ["$|$", ",", "$update$", "or", "and"],
    [Cartesian], $circ$, [($=$, $eq.not$), ($<$, $lt.eq$, $>$, $gt.eq$), ($+$, $-$), ($*$, $\/$), $\%$]
  ),
  caption: [
    Binary operators, given in order of increasing precedence.
    Operators surrounded by parentheses have equal precedence.
  ],
) <tab:binops>

A _filter definition_ has the shape
"$f(x_1; dots; x_n) := g$".
Here, $f$ is an $n$-ary filter where $g$ may refer to $x_i$.
For example, this allows us to define filters that produce the booleans,
by defining $"true" := (0 = 0)$ and $"false" := (0 eq.not 0)$.

A value $v$ is defined by
$ v := "true" | "false" | n | [v, ..., v] $
where $n$ is an integer.
While this captures only a subset of JSON values,
it provides a solid base to specify semantics such that
they are relatively straightforward to extend to the full set of JSON values.

= Semantics <semantics>

The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.

Let us start with a few definitions.
A context is a mapping from variables to values.
A value result is either a value or an error $bot$.
A stream of value results is written as $angle.l v_0, dots, v_n angle.r$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.

We are now going to introduce a few helper functions.
The first function transform a stream into
an array if all stream elements are values, or into
the leftmost error
#footnote[In these simplified semantics, we have only a single kind of error, $bot$,
  so it might seem pointless to specify which error we return.
  However, in an implementation, we may have different kinds of errors.]
in the stream otherwise:

$ [angle.l v_0, dots, v_n angle.r] = cases(
  [v_0, dots, v_n]       & "if for all " i", " v_i eq.not bot,
  v_(min{i | v_i = bot}) & "otherwise"
) $
The next function helps define filters such as if-then-else, conjunction, and disjunction:
$ "ite"(v, i, t, e) = cases(
  angle.l bot angle.r & "if " v = bot,
  t & "if " v eq.not bot " and " v = i,
  e & "otherwise"
) $
The last function serves to retrieve the $i$-th element from a list, if it exists:
$ v[i] = cases(
  v_i & "if " v = [v_0, dots, v_n] " and " 0 lt.eq i < n,
  bot & "otherwise"
) $

To evaluate calls to filters that have been introduced by definition,
we define the substitution $phi.alt[f_1 / x_1, dots, f_n / x_n]$ to be
$sigma phi.alt$, where
$sigma = {x_1 |-> f_1, dots, x_n |-> f_n}$.
The substitution $sigma phi.alt$ is defined in @tab:substitution:
It both applies the substitution $sigma$ and
replaces all variables bound in $phi.alt$ by fresh ones.
This prevents variable bindings in $phi.alt$ from
shadowing variables that occur in the co-domain of $sigma$.

#example[
  Consider the filter "$0 "as" var(x) | f(var(x))$", where "$f(g) := 1 "as" var(x) | g$".
  Here, "$f(var(x))$" expands to "$1 "as" var(x') | var(x)$", where "$var(x')$" is a fresh variable.
  The whole filter expands to "$0 "as" var(x) | 1 "as" var(x') | var(x)$",
  which evaluates to 0.
  If we would (erroneously) fail to replace $var(x)$ in $f(g)$ by a fresh variable, then
  the whole filter would expand to "$0 "as" var(x) | 1 "as" var(x) | var(x)$",
  which evaluates to 1.
]

#figure(
  table(
    columns: 2,
    $phi.alt$, $sigma phi.alt$,
    [$.$, $n$ (where $n in bb(Z)$), or $.[]$], $phi.alt$,
    [$var(x)$ or $x$], $sigma (phi.alt)$,
    $.[f]$, $.[sigma f]$,
    $f?$, $(sigma f)?$,
    $f star g$, $sigma f star sigma g$,
    $f circ g$, $sigma f circ sigma g$,
    $"if" f "then" g "else" h$, $"if" sigma f "then" sigma g "else" sigma h$,
    $x(f_1; dots; f_n)$, $x(sigma f_1; dots; sigma f_n)$,
    $f "as" var(x) | g$, $sigma f "as" var(x') | sigma' g$,
    // TODO: correctly render xs and init, see https://github.com/typst/typst/issues/1125
    $phi med x "as" var(x) (y_0; f)$, $phi med sigma x "as" var(x')(sigma y_0; sigma' f)$
  ),
  caption: [
    Substitution. Here,
    $var(x')$ is a fresh variable and
    $sigma' = sigma{var(x) |-> var(x')}$.
  ]
) <tab:substitution>

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi.alt$, $phi.alt|^c_v$,
  $"empty"$, $angle.l angle.r$,
  $.$, $angle.l v angle.r$,
  [$n$ (where $n in bb(Z)$)], $angle.l n angle.r$,
  $var(x)$, $angle.l c(var(x)) angle.r$,
  $[f]$, $angle.l [f|^c_v] angle.r$,
  $f, g$, $f|^c_v + g|^c_v$,
  $f | g$, $sum_(x in f|^c_v) g|^c_x$,
  $f "as" var(x) | g$, $sum_(x in f|^c_v) g|^(c{var(x) |-> x})_v$,
  $f circ g$, $sum_(x in f|^c_v) sum_(y in g|^c_v) angle.l x circ y angle.r$,
  $f?$, $sum_(x in f|^c_v) cases(
    angle.l angle.r & "if " x = bot,
    angle.l x angle.r & "otherwise"
  )$,
  $f "and" g$, $sum_(x in f|^c_v) "ite"(x, "false", angle.l "false" angle.r, g|^c_v)$,
  $f "or"  g$, $sum_(x in f|^c_v) "ite"(x, "true" , angle.l "true"  angle.r, g|^c_v)$,
  $"if" f "then" g "else" h$, $sum_(x in f|^c_v) "ite"(x, "true", g|^c_v, h|^c_v)$,
  $.[]$, $cases(
    angle.l v_0", " dots", " v_n angle.r & "if " v = [v_0, dots, v_n],
    angle.l bot angle.r & "otherwise"
  )$,
  $.[f]$, $sum_(i in f|^c_v) angle.l v[i] angle.r$,
  $phi med x "as" var(x) (y_0; f)$, $sum_(i in y_0|^c_v) phi^c_i (x|^c_v, f)$,
  $x(f_1; dots; f_n)$, [$g[f_1 / x_1, dots, f_n / x_n]|^c_v$ if $x(x_1; dots; x_n) := g$],
  $f update g$, [see @tab:update-semantics]
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
We suppose that the Cartesian operator $circ$ is defined on pairs of values,
yielding a value result.
We have seen examples of the shown filters in @preliminaries.
The semantics diverge relatively little from the implementation in jq.
One notable exception is $f circ g$, which jq evaluates differently as
$sum_(y in g|^c_v) sum_(x in f|^c_v) angle.l x circ y angle.r$.
//The reason will be given in [](#cloning).
Note that the difference only shows when both $f$ and $g$ return multiple values.

$ phi^c_v (l, f) := cases(
  angle.l #hide("v") angle.r + sum_(x in f|^(c{var(x) |-> h})_v) phi^c_x (t, f) & "if " l = angle.l h angle.r + t " and " phi = "reduce",
  angle.l        v   angle.r + sum_(x in f|^(c{var(x) |-> h})_v) phi^c_x (t, f) & "if " l = angle.l h angle.r + t " and " phi = "for",
  angle.l        v   angle.r & "otherwise"
) $

In addition to the filters defined in @tab:eval-semantics,
we define the semantics of the two fold-like filters "reduce" and "for" as follows,
where $x$ evaluates to $angle.l x_0, dots, x_n angle.r$:

$ "reduce"   x "as" var(x) (y_0; f) =& y_0 &
  "for"      x "as" var(x) (y_0; f) =& y_0 \
|& x_0 "as" var(x) | f &
|& ., (x_0 "as" var(x) | f \
|& dots &
|& dots \
|& x_n "as" var(x) | f &
|& ., (x_n "as" var(x) | f) dots)
$

Both filters fold $f$ over the sequence given by $x$ with the initial value $y_0$.
Their main difference is that "reduce" returns only the final value(s),
whereas "for" also returns all intermediate ones.

The following property can be used to eliminate bindings.

#lemma[
  Let $phi.alt(f)$ be a filter such that $phi.alt(f)|^c_v$ has the shape
  "$sum_(x in f|^c_v) dots$".
  Then $phi.alt(f)$ is equivalent to "$f "as" var(x) | phi.alt(var(x))$".
]

#proof[
  We have to prove the statement for $phi.alt(f)$ set to
  "$f | g$", "$f "as" var(x) | g$", "$f circ g$", "$f?$",
  "$f "and" g$", "$f "or" g$", "$"if" f "then" g "else" h$",
  "$.[f]$", and "$phi med x "as" var(x)(f; g)$".
  Let us consider the filter $phi.alt(f)$ to be $.[f]$.
  Then we show that $.[f]$ is equivalent to $f "as" var(x) | .[var(x)]$:
  $ (f "as" var(x) | .[var(x)])|^c_v
  &= sum_(x in f|^c_v) .[var(x)]|^(c{var(x) |-> x})_v \
  &= sum_(x in f|^c_v) sum_(i in var(x)|^(c{var(x) |-> x})_v) angle.l v[i] angle.r \
  &= sum_(x in f|^c_v) sum_(i in angle.l x angle.r) angle.l v[i] angle.r \
  &= sum_(x in f|^c_v) angle.l v[x] angle.r \
  &= .[f]|^c_v
  $
  The other cases for $phi.alt(f)$ can be proved similarly.
]

The semantics of jq and those shown in @tab:eval-semantics
differ most notably in the case of updates; that is, $f update g$.
We are going to deal with this in @updates.

== Updates <updates>

jq's update mechanism works with _paths_.
A path is a sequence of indices $i_j$ that can be written as $.[i_1]dots[i_n]$.
It refers to a value that can be retrieved by the filter "$.[i_1] | dots | .[i_n]$".
Note that "$.$" is a valid path, referring to the input value.

The update operation "$f update g$" attempts to
first obtain the paths of all values returned by $f$,
then for each path, it replaces the value at the path by $g$ applied to it.
Note that $f$ is not allowed to produce new values; it may only return paths.

#example[
  Consider the input value $[[1, 2], [3, 4]]$.
  We can retrieve the arrays $[1, 2]$ and $[3, 4]$ from the input with the filter "$.[]$", and
  we can retrieve the numbers 1, 2, 3, 4 from the input with the filter "$.[] | .[]$".
  To replace each number with its successor, we run "$(.[] | .[]) update .+1$",
  obtaining $[[2, 3], [4, 5]]$.
  Internally, in jq, this first builds the paths
  $.[0][0]$, $.[0][1]$, $.[1][0]$, $.[1][1]$,
  then updates the value at each of these paths with $g$.
]

There are several problems with this approach to updates:
One of these problems is that if $g$ returns no output,
the collected paths may point to values that do not exist any more.

#example[
  Consider the input value $[1, 2, 2, 3]$ and the filter
  "$.[] update g$", where $g$ is "$"if" . = 2 "then" "empty" "else" .$",
  which we might suppose to delete all values equal to 2 from the input list.
  However, the output of jq is $[1, 2, 3]$.
  What happens here is perhaps unexpected,
  but consistent with the above explanation of jq's semantics:
  jq builds the paths $.[0]$, $.[1]$, $.[2]$, and $.[3]$.
  Next, it applies $g$ to all paths.
  Applying $g$ to $.[1]$ removes the first occurrence of the number 2 from the list,
  leaving the list $[1, 2, 3]$ and the paths $.[2]$, $.[3]$ to update.
  However, $.[2]$ now refers to the number 3, and $.[3]$ points beyond the list.
] <ex:update>

Even if this particular example can be executed correctly with a special case for
filters that do not return exactly one output,
there are more general examples which this approach treats in unexpected ways.

#example[
  Consider the input value $[[0]]$ and the filter
  "$(.[], med .[][]) update g$", where $g$ is "$"if" . = [0] "then" [1, 1] "else" .+1$".
  Executing this filter in jq first builds the path
  $.[0]$ stemming from "$.[]$", then
  $.[0][0]$ stemming from "$.[][]$".
  Next, executing $g$ on the first path yields the intermediate result
  $[[1, 1]]$.
  Now, executing $g$ on the remaining path yields $[[2, 1]]$,
  instead of $[[2, 2]]$ as we might have expected.
] <ex:update-comma>

The general problem here is that the execution of the filter $g$ changes the input value,
yet only the paths constructed from the initial input are considered.
This leads to
paths pointing to the wrong data,
paths pointing to non-existent data (both occurring in @ex:update), and
missing paths (@ex:update-comma).

I now show different semantics that avoid this problem,
by interleaving calls to $f$ and $g$.
By doing so, these semantics can abandon the idea of paths altogether.

The semantics use a helper function that takes an input array $v$ and
replaces its $i$-th element by the output of $sigma$ applied to it:
$ (.[i] update sigma)|^c_v = cases(
  [angle.l v_0, dots, v_(i-1) angle.r + sigma|^c_(v_i) + angle.l v_(i+1), dots, v_n angle.r]
    & "if " v = [v_0, dots, v_n] " and " 0 lt.eq i < n,
  bot & "otherwise"
) $

// μονοπάτι = path
// συνάρτηση = function

#figure(caption: [Update semantics. Here, $var(x')$ is a fresh variable.], table(columns: 2,
  $mu$, $mu update sigma$,
  $"empty"$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $f "as" var(x) | g$, $"reduce" f "as" var(x') (.; g[var(x') / var(x)] update sigma)$,
  $"if" f "then" g "else" h$, $"reduce" f "as" var(x') (.; "if" var(x') "then" g update sigma "else" h update sigma)$,
  $.[f]$, $"reduce" f "as" var(x') (.; .[var(x')] update sigma)$,
  $.[]$, $[.[] | sigma]$,
  $x(f_1; dots; f_n)$, $g[f_1 / x_1, dots, f_n / x_n] update sigma "if" x(x_1; dots; x_n) := g$,
)) <tab:update-semantics>

The update semantics are given in @tab:update-semantics.
The case for $f "as" var(x) | g$ is slightly tricky:
Here, the intent is that $g$ has access to $var(x)$, but $sigma$ does not.
This is to ensure compatibility with jq's original semantics,
which execute $mu$ and $sigma$ independently,
so $sigma$ should not be able to access variables bound in $mu$.
In order to ensure that, we
replace $var(x)$ by a fresh variable $var(x')$ and
substitute $var(x)$ by $var(x')$ in $g$.

#example[
  Consider the filter $0 "as" var(x) | (1 "as" var(x) | .[var(x)]) update var(x)$.
  This updates the input array at index $1$.
  If the right-hand side of "$update$"
  had access to variables bound on the right-hand side,
  then the array element would be replaced by $1$,
  because the variable binding $0 "as" var(x)$ would be shadowed by $1 "as" var(x)$.
  However, because we enforce that
  the right-hand side does not have access to variables bound on the right-hand side,
  the array element is replaced by $0$, which is the value originally bound to $var(x)$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.
]

/*
We can define the plain assignment filter "$f = g$" by
"$. \as var(x) \mid f \update (var(x) \mid g)$", where
$var(x)$ may not occur free in $f$ or $g$.
The difference between "$f \update g$" and "$f = g$" is: where
"$f \update g$" replaces all values $v$ at positions $f$ by $g$ applied to $v$,
"$f = g$" replaces all values   at positions $f$ by $g$ applied to the _same_ value,
namely the input value of "$f = g$".
*/

= Conclusion

In summary, the given semantics are easier to define and to reason about,
while keeping compatibility with the original semantics in most use cases.
/*
Furthermore, avoiding to construct paths also appears to
be more performant, as I will show in [](#evaluation).
*/


#bibliography("literature.bib")
