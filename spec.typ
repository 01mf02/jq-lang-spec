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
#set par(
  first-line-indent: 1em,
  justify: true,
)
#set raw(lang: "jq")

#let thm(x, y, ..args) = thmplain(x, y, inset: (left: 0em, right: 0em), args)
#let example = thm("example", "Example")
#let lemma = thm("theorem", "Lemma")
#let proof = thm("proof", "Proof",
  bodyfmt: body => [
    #body #h(1fr) $square$    // Insert QED symbol
  ]
).with(numbering: none)

#let stream(..xs) = $angle.l #xs.pos().join($, $) angle.r$
#let var(x) = $\$#x$
#let cartesian = math.op($circle.small$)
#let arith = math.op($dot.circle$)
#let mod = math.op($\%$)
#let aritheq = math.op($dot.circle#h(0pt)=$)
#let fold = math.op($phi.alt$)
#let update = $models$
#let alt = $slash.double$
#let alteq = math.op($alt#h(0pt)=$)
#let breakr(x, v) = $"break"(\$#x, #v)$

= TODO:

- fix QED at end of proof
- fix substitution syntax
- extend to full JSON
- constant filter (string, number)
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
- literature research
- try-catch and ? are different from jq, but can be simulated via label-break
- exception = error or break
- evaluation for $alt$
- remove some filter cases in proof of lemma --- it's not exhaustive anyway right now


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

An object is a unordered map from strings to values that we write as
${k_1 |-> v_1, ..., k_n |-> v_n}$.
We also refer to the domain of an object as _keys_.
We assume that the union of two objects is _right-biased_; i.e.,
if we have two objects $l$ and $r = {k |-> v, ...}$, then $(l union r)(k) = v$
(regardless of what $l(k)$ might yield).

By convention, we write
$v$ for values,
$n$ for numbers,
$c$ for characters, and
$k$ for object keys.

A stream (or lazy list) is written as $stream(v_0, ..., v_n)$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.

We suppose that there exists a function $"error"(v)$ that
converts a value into an error.
In the remainder of this text, we will write just "error"
to denote calling $"error"(v)$ with some value $v$.
This is done such that this specification does not need to fix
the precise error value that is returned when an operation fails.

A value result is either a value or an exception.
In this section, we will see several functions that take a fixed number of values.
For any of these functions $f(v_1, ..., v_n)$,
we extend their domain to value results such that $f(v_1, ..., v_n)$ yields $v_i$
if $v_i$ is an exception and for all $j < i$, $v_j$ is a value.

The next function $[dot]$ transforms a stream into
an array if all stream elements are values, or into
the first exception in the stream otherwise:

$ [stream(v_0, ..., v_n)] := cases(
  v_i & "if" v_i "is an exception and for all" j < i", " v_j "is a value",
  [v_0, ..., v_n] & "otherwise",
) $

Given two values $k$ and $v$, we can make an object out of them:

$ {k: v} := cases(
  {k |-> v} & "if" k "is a string and" v "is a value",
  "error" & "otherwise",
) $

Given two streams of value results $k_i$ and $v_i$,
we can construct a stream of objects:#footnote[
  Note that in this definition, we use the fact that functions like
  ${l: r}$ and $l union r$ yield an exception if either $l$ or $r$ is an exception,
  as mentioned in the beginning of the section.
]

$ {k_1: v_1, ..., k_n: v_n} := cases(
  sum_(k in k_1) sum_(v in v_1) sum_(r in {k_2: v_2, ..., k_n: v_n}) stream({k: v} union r) & "if" n > 0,
  stream({}) & "otherwise"
) $

If $n > 0$, then ${k_1: v_1, ..., k_n: v_n}$ is equivalent to
$ sum_(k_1 in k_1) sum_(v_1 in v_1) ... sum_(k_n in k_n) sum_(v_n in v_n)
stream({k_1: v_1} union ... union {k_n: v_n}). $


== Simple functions

We are now going to define several functions that take values and return a value.

The domain of a value is defined as follows:

$ "dom"(v) := cases(
  stream(0  , ...,   n) & "if" v = [v_0, ..., v_n],
  stream(k_0, ..., k_n) & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n},
  "error"         & "otherwise",
) $

We define the _length_ of a value as follows:

$ |v| := cases(
  0       & "if" v = "null",
  |n|     & "if" v "is a number" n,
  n       & "if" v = c_1...c_n,
  n       & "if" v = [v_1, ..., v_n],
  n       & "if" v = {k_1 |-> v_1, ..., k_n |-> v_n},
  "error" & "otherwise (if" v in {"true", "false"}")",
) $

We can draw a link between the functions here and jq:
When called with the input value $v$,
the jq filter `keys` yields $stream(["dom"(v)])$ and
the jq filter `length` yields $stream(|v|)$.


== Arithmetic operations

We define addition of two values $l$ and $r$ as follows:

$ l + r := cases(
  v & "if" l = "null" "and" r = v", or" l = v "and" r = "null",
  n_1 + n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  c_(l,1)...c_(l,m)c_(r,1)...c_(r,n) & "if" l = c_(l,1)...c_(l,m) "and" r = c_(r,1)...c_(r,n),
  [l_1, ..., l_m, r_1, ..., r_n] & "if" l = [l_1, ..., l_m] "and" r = [r_1, ..., r_n],
  l union r & "if" l = {...} "and" r = {...},
  "error" & "otherwise",
) $

#let merge = $union.dot$

$ l times r := cases(
  l + l times (r - 1) & "if" l "is a string and" r in bb(N) without {0},
  "null" & "if" l "is a string and" r = 0,
  r times l & "if" r "is a string and" l in bb(N),
  l times r & "if" l "and" r "are numbers",
  l merge r & "if" l "and" r "are objects",
  "error" & "otherwise"
) $

Here, for two objects $l$ and $r$, their _recursive merge_ $l merge r$ is defined as:

$ l merge r := cases(
  {k |-> v_l merge v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l"," v_r "are objects",
  {k |-> v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l "or" v_r "is not an object",
  {k |-> v_r} union l merge r' & "if" k in.not "dom"(l) "and" r = {k |-> v_r} union r',
  l & "otherwise (if" r = {} ")",
) $

For two values $l$ and $r$, the arithmetic operations
$l - r$, $l div r$, and $l mod r$ (modulo) yield
$m - n$, $m div n$, and $m mod n$ if $l$ and $r$ are numbers $m$ and $n$,
otherwise they yield an error.

Suppose that the jq filters
`f` and `g` yield $stream(l)$ and $stream(r)$, respectively.
Then the jq filters `f + g` and `f * g` yield
$stream(l + r)$ and $stream(l times r)$, respectively.


== Accessing

The value $v[i]$ of a value $v$ at index $i$ is defined as follows:

$ v[i] := cases(
  v_i    & "if" v = [v_0, ..., v_n] "," i in bb(N)", and" i <= n,
  "null" & "if" v = [v_0, ..., v_n] "," i in bb(N)", and" i > n,
  v[n+i] & "if" v = [v_0, ..., v_n] "," i in bb(Z) without bb(N)", and" 0 <= n+i,
  v_j    & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" k_j = i,
  "null" & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" i in.not {k_0, ..., k_n},
  "error" & "otherwise",
) $

The idea behind this indexing operator is as follows:
It returns $"null"$ if
the value $v$ does not contain a value at index $i$,
but $v$ could be _extended_ to contain one.
More formally, $v[i]$ is $"null"$ if $v eq.not "null"$ and
there exists some value $v' = v + delta$ such that $v'[i] eq.not "null"$.

$v[] := sum_(i in"dom"(v)) stream(v[i])$.

// TODO: specify what happens if i or j > n
$ v[i:j] := cases(
  [v_i, ..., v_(j-1)] & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i <= j,
  [] & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i > j,
  c_i...c_(j-1) & "if" v = c_0...c_n", " i","j in bb(N)", and" i <= j,
  quote quote & "if" v = c_0...c_n", " i","j in bb(N)", and" i > j,
  v[(n+i):j] & "if" |v| = n", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v[i:(n+j)] & "if" |v| = n", " j in bb(Z) without bb(N)", and" 0 <= n+j,
  e & "otherwise",
) $

== Updating

$ v[] update^e f = cases(
  [f(v_0) + ... + f(v_n)] & "if" v = [v_0, ..., v_n],
  {stream(k_0): f(v_0), ..., stream(k_n): f(v_n)} & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n},
  e & "otherwise",
) $

The next function takes a value $v$ and replaces its $i$-th element by the output of $f$,
where $f$ is a function from a value to a stream of value results:
$ v[i] update^e f = cases(
  v[0:i] + [f(v_i)] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in bb(N)", and" i <= n,
  v[n+i] update^e f & "if" v = [v_0, ..., v_n]", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v + {i: f(v[i])} & "if" v = {...} "and" i "is a string",

  e & "otherwise",
) $

Note that this diverges from jq if $v = [v_0, ..., v_n]$ and $i > n$,
because jq fills up the array with $"null"$.

// TODO: in the next function, $f$ may return multiple values - we should only consider the first, and delete the slice if no value is returned!
// idea: helper function first(l, e) := h if l = stream(h) + t and e otherwise
// that way, we can do first(l, []) here
// but we unfortunately cannot use it to define {k: f}, because if f returns the empty list,
// we cannot provide a default element e that would make the key disappear

$ v[i:j] update^e f = cases(
  v[(n+i):j] update^e f & "if" |v| = n", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v[i:(n+j)] update^e f & "if" |v| = n", " j in bb(Z) without bb(N)", and" 0 <= n+j,
  [v_0, ..., v_(i-1)] + f(v[i:j]) + [v_(j), ..., v_n] & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i <= j,
  v & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i > j,
  // TODO: strings
  e & "otherwise",
) $

== Ordering

Now, we will establish a total order "$<$" on values.
Recall that for any total order "$<$", we can say that
$l = r$ iff neither $l < r$ nor $r < l$.

The order "$<$" on values satisfies
$ "null" < "false" < "true" < n < s < a < o, $ where
$n$ is a number,
$s$ is a string,
$a$ is an array, and
$o$ is an object.
We assume that there is a total order on numbers and characters.
Strings and arrays are compared lexicographically.

// TODO: mention that jq does not have an actual total order, due to nan < nan

Two objects $o_1$ and $o_2$ are compared as follows:
For both objects $o_i$ ($i in {1, 2}$),
we sort the array $["dom"(o_i)]$ by ascending order to obtain the ordered array of keys
$k_i = [k_1, ..., k_n]$, from which we obtain
$v_i = [o[k_1], ..., o[k_n]]$.
We then have $ o_1 < o_2 <==> cases(
  k_1 < k_2 & "if" k_1 < k_2 "or" k_1 > k_2,
  v_1 < v_2 & "otherwise" (k_1 = k_2)
) $

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

We will start by introducing high-level intermediate representation (HIR) syntax in @hir.
This syntax is very close to actual jq syntax.
Then, we will identify a subset of HIR as mid-level intermediate representation (MIR) in @mir and provide a way to translate from HIR to MIR.
This will simplify our semantics in @semantics.

#let or_ = $quad || quad$

== HIR <hir>

A _filter_ $f$ is defined by

$ f :=& n #or_ s #or_ . \
  #or_& (f) #or_ f? #or_ [f] #or_ {f: f, ..., f: f} #or_ f[p]^?...[p]^? \
  #or_& f star f #or_ f cartesian f \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (f; f) #or_ var(x) \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& "if" f "then" f "else" f #or_ "try" f "catch" f \
  #or_& x #or_ x(f; ...; f)
$
where $p$ is a path part of the shape
$ p := [] #or_ [f] #or_ [f:] #or_ [:f] #or_ [f:f]. $
Here, $x$ is an identifier (such as "empty").

By convention, we write $var(x')$ to denote a fresh variable.
The potential instances of $star$ and $cartesian$ are given in @tab:binops.
A folding operation $fold$ is either "reduce" or "for".

#figure(
  table(
    columns: 3,
    [Name], [Symbol], [Operators],
    [Complex], $star$, ["$|$", ",", ("=", "$update$", "$aritheq$", "$alteq$"), "$alt$", "or", "and"],
    [Cartesian], $cartesian$, [($eq.quest$, $eq.not$), ($<$, $<=$, $>$, $>=$), $dot.circle$],
    [Arithmetic], $dot.circle$, [($+$, $-$), ($times$, $div$), $mod$],
  ),
  caption: [
    Binary operators, given in order of increasing precedence.
    Operators surrounded by parentheses have equal precedence.
  ],
) <tab:binops>

All operators $star$ and $cartesian$ are left-associative, except for
"$|$", "$=$", "$update$", and "$aritheq$".

A _filter definition_ has the shape
"$f(x_1; ...; x_n) := g$".
Here, $f$ is an $n$-ary filter where $g$ may refer to $x_i$.
For example, this allows us to define filters that produce the booleans,
by defining $"true" := (0 = 0)$ and $"false" := (0 eq.not 0)$.

== MIR <mir>

A MIR filter $f$ has the shape
$ f :=& n #or_ s #or_ . \
  #or_& f? #or_ [f] #or_ {f: f, ..., f: f} #or_ .[p] \
  #or_& f star f #or_ var(x) cartesian var(x) \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (var(y_0); f) #or_ var(x) \
  #or_& "if" var(x) "then" f "else" f #or_ "try" f "catch" f \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& x(f; ...; f)
$
where $p$ is a path part of the shape
$ p := [] #or_ [var(x)] #or_ [var(x):var(x)]. $
Furthermore, the set of complex operators $star$ in MIR
does not include "$=$" and "$aritheq$" anymore.

Compared to HIR, MIR filters have significantly simpler path operations
($.[p]$ versus $f[p]^?...[p]^?$)
and replace certain occurrences of filters by variables
(e.g. $var(x) cartesian var(x)$ versus $f cartesian f$).

We can lower any HIR filter $phi$ to an equivalent MIR filter $floor(phi)$
using @tab:lowering.
In particular, this desugars path operations and
makes it explicit which operations are cartesian or complex.

#figure(caption: [Lowering of a	HIR filter $phi$ to a MIR filter $floor(phi)$.], table(columns: 2,
  $phi$, $floor(phi)$,
  [$n$, $s$, $.$, $var(x)$, or $"break" var(x)$], $phi$,
  $(f)$, $floor(f)$,
  $f?$, $floor(f)?$,
  $[f]$, $[floor(f)]$,
  ${f_1: g_1, ..., f_n: g_n}$, ${floor(f_1): floor(g_1), ..., floor(f_n): floor(g_n)}$,
  $f[p_1]^?...[p_n]^?$, $. "as" var(x') | floor(f) | floor([p_1]^?)_var(x') | ... | floor([p_n]^?)_var(x')$,
  $f = g$, $. "as" var(x') | floor(f update (var(x') | g))$,
  $f update g$, $floor(f) update floor(g)$,
  $f aritheq g$, $floor(f update . arith g)$,
  $f alteq g$, $floor(f update . alt g)$,
  $f "and" g$, $floor(f) "as" var(x') | var(x') "and" floor(g)$,
  $f "or"  g$, $floor(f) "as" var(x') | var(x') "or"  floor(g)$,
  $f star g$, $floor(f) star floor(g)$,
  $f cartesian g$, $floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
  // TODO: report wrong documentation on $alt$
  $f alt g$, $(floor(f) | "if" . "then" . "else" "empty") alt floor(g)$,
  $f "as" var(x) | g$, $floor(f) "as" var(x) | floor(g)$,
  $fold f_x "as" var(x) (f_y; f)$, $floor(f_y) "as" var(y') | fold floor(f_x) "as" var(x) (var(y'); floor(f))$,
  $"if" f_x "then" f "else" g$, $floor(f_x) "as" var(x') | "if" var(x') "then" floor(f) "else" floor(g)$,
  $"try" f "catch" g$, $"try" floor(f) "catch" floor(g)$,
  $"label" var(x) | f$, $"label" var(x) | floor(f)$,
  $x$, $cases(x() & "if" x := r, x & "otherwise")$,
  $x(f_1; ...; f_n)$, $x(floor(f_1); ...; floor(f_n))$,
)) <tab:lowering>

#example[
  The HIR filter $[3] | .[0] = ("length", 2)$ is lowered to the MIR filter
  $"TODO"$.
  Its output is $stream([1], [2])$.
]

We can lower path parts $[p]^?$ to MIR filters using @tab:lower-path.

#figure(caption: [Lowering of a path part $[p]^?$ with input $var(x)$ to a MIR filter.], table(columns: 2, align: left,
  $[p  ]^?$, $floor([p]^?)_var(x)$,
  $[   ]^?$, $.[]^?$,
  $[f  ]^?$, $(var(x) | floor(f)) "as" var(y') | .[var(y')]^?$,
  $[f: ]^?$, $(var(x) | floor(f)) "as" var(y') | "length"^? "as" var(z') | .[var(y') : var(z')]^?$,
  $[ :f]^?$, $(var(x) | floor(f)) "as" var(y') | 0 "as" var(z') | .[var(z') : var(y')]^?$,
  $[f:g]^?$, $(var(x) | floor(f)) "as" var(y') | (var(x) | floor(g)) "as" var(z') | .[var(y') : var(z')]^?$,
)) <tab:lower-path>



= Evaluation Semantics <semantics>

The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.

Let us start with a few definitions.
A context $c$ is a mapping
from variables $var(x)$ to values and
from identifiers $x$ to pairs $(f, c)$, where $f$ is a filter and $c$ is a context.
Contexts store to what variables and filter arguments are bound.

We are now going to introduce a few helper functions.
The next function helps define filters such as if-then-else, conjunction, and disjunction:
$ "ite"(v, i, t, e) = cases(
  t & "if" v = i,
  e & "otherwise"
) $

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $phi|^c_v$,
  $"empty"$, $stream()$,
  $.$, $stream(v)$,
  [$n$ (where $n in bb(Z)$)], $stream(n)$,
  $var(x)$, $stream(c(var(x)))$,
  $[f]$, $stream([f|^c_v])$,
  $f, g$, $f|^c_v + g|^c_v$,
  $f | g$, $sum_(x in f|^c_v) g|^c_x$,
  $f "as" var(x) | g$, $sum_(x in f|^c_v) g|^(c{var(x) |-> x})_v$,
  $var(x) cartesian var(y)$, $stream(c(var(x)) cartesian c(var(y)))$,
  $f?$, $sum_(x in f|^c_v) cases(
    stream() & "if" x "is an error",
    stream(x) & "otherwise"
  )$,
  $var(x) "and" f$, $"ite"(c(var(x)), "false", stream("false"), f|^c_v)$,
  $var(x) "or"  f$, $"ite"(c(var(x)), "true" , stream("true" ), f|^c_v)$,
  $"if" var(x) "then" f "else" g$, $"ite"(c(var(x)), "true", f|^c_v, g|^c_v)$,
  $.[]$, $v[]$,
  $.[var(x)]$, $stream(v[c(var(x))])$,
  $.[var(x):var(y)]$, $stream(v[c(var(x)):c(var(y))])$,
  $fold x "as" var(x) (var(y); f)$, $fold^c_c(var(y)) (x|^c_v, var(x), f)$,
  $x(f_1; ...; f_n)$, $g|^(c{x_1 |-> f_1, ..., x_n |-> f_n})_v "if" x(x_1; ...; x_n) := g$,
  $x$, $f|^c'_v "if" c(x) = (f, c')$,
  $f update g$, [see @updates]
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
We suppose that the Cartesian operator $cartesian$ is defined on pairs of values,
yielding a value result.
We have seen examples of the shown filters in @preliminaries.
The semantics diverge relatively little from the implementation in jq.
One notable exception is $f cartesian g$, which jq evaluates differently as
$sum_(y in g|^c_v) sum_(x in f|^c_v) stream(x cartesian y)$.
//The reason will be given in [](#cloning).
Note that the difference only shows when both $f$ and $g$ return multiple values.

$ "fold"^c_v (l, var(x), f, o) := cases(
  o(v) + sum_(x in f|^(c{var(x) |-> h})_v) "fold"^c_x (t, var(x), f, o) & "if" l = stream(h) + t,
  stream(        v ) & "otherwise" (l = stream())
) $

$ "foreach"^c_v (l, var(x), f) := cases(
  sum_(x in f|^(c{var(x) |-> h})_v) "for"(t, var(x), f) & "if" l = stream(h) + t,
  stream() & "otherwise",
) $

$ "reduce"^c_v (l, var(x), f) :=& "fold"(l, var(x), f, o) "where" o(v) = stream(#hide[v]) \
     "for"^c_v (l, var(x), f) :=& "fold"(l, var(x), f, o) "where" o(v) = stream(v)
$

In addition to the filters defined in @tab:eval-semantics,
we define the semantics of the two fold-like filters "reduce" and "for" as follows,
where $x$ evaluates to $stream(x_0, ..., x_n)$:

$ "reduce"   x "as" var(x) (y_0; f) =& y_0 &
  "for"      x "as" var(x) (y_0; f) =& y_0 \
|& x_0 "as" var(x) | f &
|& ., (x_0 "as" var(x) | f \
|& ... &
|& ... \
|& x_n "as" var(x) | f &
|& ., (x_n "as" var(x) | f)...)
$

$ "foreach" x "as" var(x) (y_0; f) =& y_0 \
|& x_0 "as" var(x) | f \
|& ., (x_1 "as" var(x) | f \
|& ... \
|& ., (x_n "as" var(x) | f)...)
$

// TODO: mention that folding considers only first(f)

Both filters fold $f$ over the sequence given by $x$ with the initial value $y_0$.
Their main difference is that "reduce" returns only the final value(s),
whereas "for" also returns all intermediate ones.

The following property can be used to eliminate bindings.

#lemma[
  Let $phi(f)$ be a filter such that $phi(f)|^c_v$ has the shape
  "$sum_(x in f|^c_v) ...$".
  Then $phi(f)$ is equivalent to "$f "as" var(x) | phi(var(x))$".
]

#proof[
  We have to prove the statement for $phi(f)$ set to
  "$f | g$", "$f "as" var(x) | g$", "$f cartesian g$", "$f?$",
  "$f "and" g$", "$f "or" g$", "$"if" f "then" g "else" h$",
  "$.[f]$", and "$fold x "as" var(x)(f; g)$".
  Let us consider the filter $phi(f)$ to be $.[f]$.
  Then we show that $.[f]$ is equivalent to $f "as" var(x) | .[var(x)]$:
  $ (f "as" var(x) | .[var(x)])|^c_v
  &= sum_(x in f|^c_v) .[var(x)]|^(c{var(x) |-> x})_v \
  &= sum_(x in f|^c_v) sum_(i in var(x)|^(c{var(x) |-> x})_v) stream(v[i]) \
  &= sum_(x in f|^c_v) sum_(i in stream(x)) stream(v[i]) \
  &= sum_(x in f|^c_v) stream(v[x]) \
  &= .[f]|^c_v
  $
  The other cases for $phi(f)$ can be proved similarly.
]

The semantics of jq and those shown in @tab:eval-semantics
differ most notably in the case of updates; that is, $f update g$.
We are going to deal with this in @updates.

= Update Semantics <updates>

jq's update mechanism works with _paths_.
A path is a sequence of indices $i_j$ that can be written as $.[i_1]...[i_n]$.
It refers to a value that can be retrieved by the filter "$.[i_1] | ... | .[i_n]$".
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

// μονοπάτι = path
// συνάρτηση = function

// TODO:
// - explain that sigma is now a function, not a filter
// - make "reduce"^c_v explicit about the name of the variable $x

#figure(caption: [Update semantics. Here, $mu$ is a filter and $sigma(v)$ is a function from a value $v$ to a stream of value results.], table(columns: 2,
  $mu$, $(mu update sigma)|^c_v$,
  $"empty"$, $stream(v)$,
  $.$, $sigma(v)$,
  $f | g$, $(f update sigma')|^c_v "where" sigma'(x) = (g update sigma)|^c_x$,
  $f, g$, $sum_(x in (f update sigma)|^c_v) (g update sigma)|^c_x$,
  $f alt g$, $"ite"(sum_(x in f|^c_v, med x in.not {"null", "false"}) stream(x), stream(), (g update sigma)|^c_v, (f update sigma)|^c_v)$,
  // TODO: mention how to extend c to c(p)
  $.[p]$, $stream(v[c(p)] update^e sigma(v)) "where" e = "error"$,
  $f "as" var(x) | g$, $"reduce"^c_v (f|^c_v, var(x), (g update sigma))$,
  $"if" var(x) "then" f "else" g$, $"ite"(c(var(x)), "true", (f update sigma)|^c_v, (g update sigma)|^c_v)$,
  $"try" f "catch" g$, $sum_(x in (f update sigma)|^c_v) "catch"(x, g, c)$,
  $"label" var(x) | f$, $"label"(var(x), f update sigma)$,
  $"break" var(x)$, $stream(breakr(x, v))$,
  $x(f_1; ...; f_n)$, $(g update sigma)|^(c{x_1 |-> f_1, ..., x_n |-> f_n})_v "if" x(x_1; ...; x_n) := g$,
  $x$, $(f update sigma)|^c'_v "if" c(x) = (f, c')$,
)) <tab:update-semantics>

$ "label"(var(x), l) := cases(
  stream(v) & "if" l = stream(breakr(x, v)) + t,
  stream(h) + "label"(var(x), t) & "if" l = stream(h) + t "and" h eq.not breakr(x, v),
  stream() & "if" l = stream(),
) $

$ "catch"(x, g, c) := cases(
    // TODO: is "tostring" correct here?
    sum_(e in g|^c_("tostring"(x))) stream("error"(e)) & "if" x "is an unpolarised error",
    stream(x) & "otherwise"
) $

#figure(caption: [Update semantics properties.], table(columns: 2,
  $mu$, $mu update sigma$,
  $"empty"$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $"if" var(x) "then" f "else" g$, $"if" var(x) "then" f update sigma "else" g update sigma$,
)) <tab:update-props>

For two filters $f$ and $g$, we define
$(f update g)|^c_v := sum_(y in (f update sigma)|^c_v) "depolarise"(y)$, where
$sigma(x) = sum_(y in g|^c_x) "polarise"(y)$.
The function "polarise" marks exceptions occurring in the filter $g$,
and "depolarise" removes the marker from exceptions.

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
