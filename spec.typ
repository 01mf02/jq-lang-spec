#import "@preview/ctheorems:1.1.0": thmplain, thmrules
#import "@preview/diagraph:0.2.1"
#import "article.typ": article
#import "acm.typ": acmart
#show: thmrules

#show: acmart.with(
  format: "acmsmall",
  title: [A formal specification of the jq language],
  authors: (
    (
      name: "Michael Färber",
      email: "michael.faerber@gedenkt.at",
      orcid: "0000-0003-1634-9525",
      affiliation: none,
    ),
  ),
  authors-short: "Färber",
  ccs: (
    ([Software and its engineering], (
      (500, [Semantics]),
      (500, [Functional languages]),
    )),
  ),
  abstract: [
    jq is a widely used tool that provides a programming language to manipulate JSON data.
    However, it is currently only specified by its implementation,
    making it difficult to reason about its behaviour.
    To this end, we provide a syntax and denotational semantics for
    a large subset of the jq language.
    Our most significant contribution is to provide a new way to interpret updates
    that allows for more predictable and performant execution.
  ],
  keywords: ("JSON", "semantics"),

  pub: (
    journal: "Journal of the ACM",
    journal-short: "J. ACM",
    volume: 37,
    number: 4,
    article: 1,
    month: 8,
    year: 2018,
    doi: "XXXXXXX.XXXXXXX",
  )
)

#set figure(placement: auto)
#set raw(lang: "jq")

#let thm(x, y, ..args) = thmplain(x, y, inset: (left: 0em, right: 0em), args)
#let example = thm("example", "Example")
#let lemma = thm("theorem", "Lemma")
#let proof = thm("proof", "Proof",
  bodyfmt: body => [
    #body #h(1fr) $square$    // Insert QED symbol
  ]
).with(numbering: none)

#let or_ = $quad || quad$
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

#let qs(s) = $quote #s quote$
#let oat(k) = $.[#qs(k)]$

/*
TODO:
- fix QED at end of proof
- literature research
- completeness is if we can construct any valid value
- explain difference between $x$ and $x(...)$
- explain `main`
*/


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
However, the documentation frequently does not cover certain cases, and
historically, the implementation often downright contradicted the documentation.
/*
For example, the documentation stated that the filter `limit(n; f)`
"extracts up to `n` outputs from `f`".
However, `limit(0; f)` extracts up to 1 outputs from `f`, and
for negative values of `n`, `limit(n; f)` extracts all outputs of `f`.
*/
The underlying issue is that there existed no formally specified semantics to rely on.
Having such semantics allows to determine whether
certain behaviour of a jq implementation is accidental or intended.

However, a formal specification of the behaviour of jq would be very verbose,
because jq has many special cases whose merit is not apparent.
Therefore, I have striven to create
denotational semantics (@semantics) that closely resemble those of jq such that
in most cases, their behaviour coincides, whereas they may differ in more exotic cases.
The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe, understand, and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.

One particular improvement over jq are the new update semantics (@updates), which
are simpler to describe and implement,
eliminate a range a potential errors, and
allow for more performant execution.

The structure of this text is as follows:
@tour introduces jq by a series of examples that
give a glimpse of actual jq syntax and behaviour.
From that point on, the structure of the text follows
the execution of a jq program as shown in @fig:structure.
@syntax formalises a subset of jq syntax and shows how jq syntax can be
transformed to increasingly low-level intermediate representations called
HIR (@hir) and MIR (@mir).
After this, the semantics part starts:
@values defines the type of JSON values and the elementary operations that jq provides for it.
Furthermore, it defines other basic data types such as errors, exceptions, and streams.
@semantics shows how to evaluate jq filters on a given input value.
@updates then shows how to evaluate a class of jq filters that update values using
a filter called _path_ that defines which parts of the input to update, and
a filter that defines what the values matching the path should be replaced with.

#figure(caption: [Evaluation of a jq program with an input value.
  Solid lines indicate data flow, whereas a dashed line indicates that
  a component is defined in terms of another.
], diagraph.render(read("structure.dot"))) <fig:structure>

= Tour of jq <tour>

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

We can define filters by using the syntax "`def f(x1; ...; xn): g;`",
which defines an filter `f` taking `n` arguments by `g`,
where `g` can refer to `x1` to `xn`.
For example, jq provides the filter "`recurse(f)`" to calculate fix points,
which could be defined by "`def recurse(f): ., (f | recurse(f));`".
Using this, we can define a filter to calculate the factorial function, for example.

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



= Syntax <syntax>

This section describes the syntax for a subset of the jq language
that will be used later to define the semantics in @semantics.
To set the formal syntax apart from
the concrete syntax introduced in @tour,
we use cursive font (as in "$f$", "$v$") for the specification
instead of the previously used typewriter font (as in "`f`", "`v`").

We will start by introducing high-level intermediate representation (HIR) syntax in @hir.
This syntax is very close to actual jq syntax.
Then, we will identify a subset of HIR as mid-level intermediate representation (MIR) in @mir and provide a way to translate from HIR to MIR.
This will simplify our semantics in @semantics.
Finally, in @jq-syntax, we will show how HIR relates to actual jq syntax.

== HIR <hir>

A _filter_ $f$ is defined by

$ f :=& n #or_ s #or_ . \
  #or_& (f) #or_ f? #or_ [f] #or_ {f: f, ..., f: f} #or_ f[p]^?...[p]^? \
  #or_& f star f #or_ f cartesian f \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (f; f) #or_ var(x) \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& "if" f "then" f "else" f #or_ "try" f "catch" f \
  #or_& x #or_ x(f; ...; f)
$ where
$p$ is a path part of the shape $ p := [] #or_ [f] #or_ [f:] #or_ [:f] #or_ [f:f], $
$x$ is an identifier (such as "empty"),
$n$ is a number (such as $42$ or $3.14$), and
$s$ is a string (such as "Hello world!").

// TODO: explain meaning of $^?$
By convention, we write $var(x')$ to denote a fresh variable.
The potential instances of $star$ and $cartesian$ are given in @tab:binops.
A folding operation $fold$ is either "reduce" or "foreach".

#figure(
  table(
    columns: 3,
    [Name], [Symbol], [Operators],
    [Complex], $star$, ["$|$", ",", ("=", "$update$", "$aritheq$", "$alteq$"), "$alt$", "or", "and"],
    [Cartesian], $cartesian$, [($eq.quest$, $!=$), ($<$, $<=$, $>$, $>=$), $dot.circle$],
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
by defining $"true" := (0 = 0)$ and $"false" := (0 != 0)$.

We are assuming a few preconditions that must be fulfilled for a filter to be well-formed.
For this, we consider a definition $x(x_1; ...; x_n) := phi$:

- Arguments must be bound:
  The only filter arguments that $phi$ can refer to are $x_1, ..., x_n$.
- Labels must be bound:
  If $phi$ contains a statement $"break" var(x)$,
  then it must occur as a subterm of $g$, where
  $"label" var(x) | g$
  is a subterm of $phi$.
- Variables must be bound:
  If $phi$ contains any occurrence of a variable $var(x)$,
  then it must occur as a subterm of $g$, where either
  $f "as" var(x) | g$ or
  $fold x "as" var(x) (y; g)$
  is a subterms of $phi$.

== MIR <mir>

We are now going to identify a subset of HIR called MIR and
show how to _lower_ a HIR filter to a semantically equivalent MIR filter.

A MIR filter $f$ has the shape
$ f :=& n #or_ s #or_ . \
  #or_& [f] #or_ {} #or_ {f: f} #or_ .[p] \
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

We can lower any HIR filter $phi$ to a semantically equivalent MIR filter $floor(phi)$
using @tab:lowering.
In particular, this desugars path operations and
makes it explicit which operations are Cartesian or complex.
We can lower path parts $[p]^?$ to MIR filters using @tab:lower-path.

#figure(caption: [Lowering of a	HIR filter $phi$ to a MIR filter $floor(phi)$.], table(columns: 2,
  $phi$, $floor(phi)$,
  [$n$, $s$, $.$, $var(x)$, or $"break" var(x)$], $phi$,
  $(f)$, $floor(f)$,
  $f?$, $"try" floor(f) "catch" "empty"$,
  $[]$, $["empty"]$,
  $[f]$, $[floor(f)]$,
  ${}$, ${}$,
  ${f: g}$, $floor(f) "as" var(x') | floor(g) "as" var(y') | {var(x'): var(y')}$,
  ${f_1: g_1, ..., f_n: g_n}$, $floor(sum_i {f_i: g_i})$,
  $f[p_1]^?...[p_n]^?$, $. "as" var(x') | floor(f) | floor([p_1]^?)_var(x') | ... | floor([p_n]^?)_var(x')$,
  $f = g$, $. "as" var(x') | floor(f update (var(x') | g))$,
  $f update g$, $floor(f) update floor(g)$,
  $f aritheq g$, $floor(f update . arith g)$,
  $f alteq g$, $floor(f update . alt g)$,
  $f "and" g$, $floor(f) "as" var(x') | var(x') "and" floor(g)$,
  $f "or"  g$, $floor(f) "as" var(x') | var(x') "or"  floor(g)$,
  $f star g$, $floor(f) star floor(g)$,
  $f cartesian g$, $floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
  $f "as" var(x) | g$, $floor(f) "as" var(x) | floor(g)$,
  $fold f_x "as" var(x) (f_y; f)$, $floor(f_y) "as" var(y') | fold floor(f_x) "as" var(x) (var(y'); floor(f))$,
  $"if" f_x "then" f "else" g$, $floor(f_x) "as" var(x') | "if" var(x') "then" floor(f) "else" floor(g)$,
  $"try" f "catch" g$, $"try" floor(f) "catch" floor(g)$,
  $"label" var(x) | f$, $"label" var(x) | floor(f)$,
  $x$, $x$,
  $x(f_1; ...; f_n)$, $x(floor(f_1); ...; floor(f_n))$,
)) <tab:lowering>

#figure(caption: [Lowering of a path part $[p]^?$ with input $var(x)$ to a MIR filter.], table(columns: 2, align: left,
  $[p  ]^?$, $floor([p]^?)_var(x)$,
  $[   ]^?$, $.[]^?$,
  $[f  ]^?$, $(var(x) | floor(f)) "as" var(y') | .[var(y')]^?$,
  $[f: ]^?$, $(var(x) | floor(f)) "as" var(y') | "length"^? "as" var(z') | .[var(y') : var(z')]^?$,
  $[ :f]^?$, $(var(x) | floor(f)) "as" var(y') | 0 "as" var(z') | .[var(z') : var(y')]^?$,
  $[f:g]^?$, $(var(x) | floor(f)) "as" var(y') | (var(x) | floor(g)) "as" var(z') | .[var(y') : var(z')]^?$,
)) <tab:lower-path>

#example[
  The HIR filter $mu eq.triple .[0]$ is lowered to
  $floor(mu) eq.triple . "as" var(x) | . | (var(x) | 0) "as" var(y) | .[var(y)]$.
  Semantically, we will see that $floor(mu)$ is equivalent to $0 "as" var(y) | .[var(y)]$.
  The HIR filter $phi eq.triple [3] | .[0] = ("length", 2)$ is lowered to the MIR filter
  $floor(phi) eq.triple [3] | . "as" var(z) | floor(mu) update (var(z) | ("length", 2))$.
  In @semantics, we will see that its output is $stream([1], [2])$.
]

This lowering assumes the presence of one filter in the definitions, namely $"empty"$.
This filter returns an empty stream.
We might be tempted to define it as ${} | .[]$,
which constructs an empty object, then returns its contained values,
which corresponds to an empty stream as well.
However, such a definition relies on the temporary construction of new values
(such as the empty object here),
which is not admissible on the left-hand side of updates (see @updates).
For this reason, we have to define it in a more complicated way, for example
$ "empty" := ({} | .[]) "as" var(x) | . $
This definition ensures that $"empty"$ can be employed also as a path expression.

This lowering is compatible with the semantics of the jq implementation,
with one notable exception:
In jq, Cartesian operations $f cartesian g$ would be lowered to
$floor(g) "as" var(y') | floor(f) "as" var(x') | var(x) cartesian var(y)$, whereas we lower it to
$floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
thus inverting the binding order.
Our lowering of Cartesian operations is consistent with that of
other operators, such as ${f: g}$, where
the leftmost filter ($f$) is bound first and the rightmost filter ($g$) is bound last.
Note that the difference only shows when both $f$ and $g$ return multiple values.

#example[
  The filter $(0, 2) + (0, 1)$ yields
  $stream(0, 1, 2, 3)$ using our lowering, and
  $stream(0, 2, 1, 3)$ in jq.
]

== Concrete jq syntax <jq-syntax>

Let us now go a level above HIR, namely a subset of actual jq syntax#footnote[
  Actual jq syntax has a few more constructions to offer, including
  nested definitions, variable arguments, string interpolation, modules, etc.
  However, these constructions can be transformed into
  semantically equivalent syntax as treated in this text.
] of which we have seen examples in @tour, and
show how to transform jq programs to HIR and to MIR.

A _program_ is a (possibly empty) sequence of definitions, followed by a single filter `f`.
A _definition_ has the shape `def x(x1; ...; xn): g;` or `def x: g`; where
`x` is an identifier,
`x1` to `xn` is a non-empty sequence of semicolon-separated identifiers, and
`g` is a filter.
In HIR, we write the corresponding definition as $x(x_1; ...; x_n) := g$.

The syntax of filters in concrete jq syntax is nearly the same as in HIR.
To translate between the operators in @tab:binops, see @tab:op-correspondence.
The arithmetic update operators in jq, namely
`+=`,
`-=`,
`*=`,
`/=`, and
`%=`,
correspond to the operators $aritheq$ in HIR, namely
$+#h(0pt)=$,
$-#h(0pt)=$,
$times#h(0pt)=$,
$div#h(0pt)=$, and
$mod#h(0pt)=$.
Filters of the shape
`if f then g else h end` correspond to the filter
$"if" f "then" g "else" h$ in HIR;
that is, in HIR, the final `end` is omitted.

#let correspondence = (
  (`|`, $|$),
  (`,`, $,$),
  (  `=`, $=$),
  ( `|=`, $update$),
  (`//=`, $alteq$),
  (`//`, $alt$),
  (`==`, $eq.quest$),
  (`!=`, $!=$),
  (`<` , $< $),
  (`<=`, $<=$),
  (`>` , $> $),
  (`>=`, $>=$),
  (`+`, $+$),
  (`-`, $-$),
  (`*`, $times$),
  (`/`, $div$),
  (`%`, $mod$),
)
#figure(caption: [Operators in concrete jq syntax and their corresponding HIR operators.], table(columns: 1+correspondence.len(),
  [jq],  ..correspondence.map(c => c.at(0)),
  [HIR], ..correspondence.map(c => c.at(1)),
)) <tab:op-correspondence>

To convert a jq program to MIR, we do the following:

+ For each definition, convert it to a HIR definition.
+ Convert the filter `f` to a HIR filter $f$.
+ Replace the right-hand sides of HIR definitions and $f$ by
  their lowered MIR counterparts, using @tab:lowering.

#example[
  Consider the jq program `def recurse(f): ., (f | recurse(f)); recurse(. + 1)`,
  which returns the infinite stream of output values $n, n+1, ...$
  when provided with an input number $n$.
  The definition in this example can be converted to the HIR definition
  $"recurse"(f) := ., (f | "recurse"(f))$ and the main filter can be converted to the HIR filter
  $"recurse"(. + 1)$.
  The lowering of the definition to MIR yields the same as the HIR definition, and
  the lowering of the main filter to MIR yields
  $"recurse"(. "as" var(x') | 1 "as" var(y') | var(x') + var(y'))$.
]

#example[
  Consider the jq program `def select(f): if f then . else empty end; def negative: . < 0; .[] | select(negative)`.
  When given an array as an input, it yields
  those elements of the array that are smaller than $0$.
  Here, the definitions in the example are converted to the HIR definitions
  $"select"(f) := "if" f "then" . "else" "empty"$ and
  $"negative"(f) := . < 0$, and
  the main filter is converted to the HIR filter
  $.[] | "select"("negative")$.
  Both the definition of $"select"(f)$ and the main filter are already in MIR;
  the MIR version of the remaining definition is
  $"negative"(f) := . "as" var(x') | 0 "as" var(y') | var(x') < var(y')$.
]

We will show in @semantics how to run the resulting MIR filter $f$
in the presence of a set of MIR definitions.
For a given input value $v$, the output of $f$ will be given by $f|^{}_v$.


= Values <values>

In this section, we will define
JSON values, errors, exceptions, and streams.
Furthermore, we will define several functions and operations on values.

A JSON value $v$ has the shape

$ v := "null" #or_ "false" #or_ "true" #or_ n #or_ s #or_ [v_0, ..., v_n] #or_ {k_0 |-> v_0, ..., k_n |-> v_n}, $

where $n$ is a number and $s$ is a string.
We write a string $s$ as $c_0...c_n$, where $c$ is a character.
A value of the shape $[v_0, ..., v_n]$ is called an _array_ and
a value of the shape ${k_0 |-> v_0, ..., k_n |-> v_n}$ is
an unordered map from _keys_ $k$ to values that we call an _object_.#footnote[
  The JSON syntax uses
  ${k_0: v_0, ..., k_n: v_n}$ instead of
  ${k_0 |-> v_0, ..., k_n |-> v_n}$.
  However, in this text, we will use the
  ${k_0: v_0, ..., k_n: v_n}$ syntax to define the _construction_ of objects, and use
  ${k_0 |-> v_0, ..., k_n |-> v_n}$ syntax to denote actual objects.
]
In JSON, object keys are strings.#footnote[
  YAML is a data format similar to JSON.
  While YAML can encode any JSON value, it additionally
  allows any YAML values to be used as object keys, where JSON
  allows only strings to be used as object keys.
  This text deliberately distinguishes between object keys and strings.
  That way, extending the given semantics to use YAML values should be relatively easy.
]
We assume that the union of two objects is _right-biased_; i.e.,
if we have two objects $l$ and $r = {k |-> v, ...}$, then $(l union r)(k) = v$
(regardless of what $l(k)$ might yield).

By convention, we will write in the remainder of this text
$v$ for values,
$n$ for numbers,
$c$ for characters, and
$k$ for object keys.

A number can be an integer or a decimal, optionally followed by an integer exponent.
For example, $0$, $-42$, $3.14$, $3 times 10^8$ are valid JSON numbers.
This text does not fix how numbers are to be represented,
just like the JSON standard does not impose any representation.#footnote[
  jq uses floating-point numbers to encode both integers and decimals.
  However, several operations in this text (for example those in @accessing)
  make only sense for natural numbers $bb(N)$ or integers $bb(Z)$.
  In situations where integer values are expected and a number $n$ is provided,
  jq generally substitutes $n$ by $floor(n)$ if $n >= 0$ and $ceil(n)$ if $n < 0$.
  For example, accessing the $0.5$-th element of an array yields its $0$-th element.
  In this text, we use do not document this rounding behaviour for each function.
]
Instead, it just assumes that the type of numbers has a total order (see @ordering) and
supports the arithmetic operations $+$, $-$, $times$, $div$, and $mod$ (modulo).

An _error_ can be constructed from a value by the function $"error"(v)$.
The $"error"$ function is bijective; that is,
if we have an error $e$, then there is a unique value $v$ with $e = "error"(v)$.
In the remainder of this text, we will write just "error"
to denote calling $"error"(v)$ with some value $v$.
This is done such that this specification does not need to fix
the precise error value that is returned when an operation fails.

An _exception_ either is an error or has the shape $"break"(var(x), v)$.
The latter will become relevant starting from @semantics.

A _value result_ is either a value or an exception.
In this text, we will see many functions that take a fixed number of values.
For any of these functions $f(v_1, ..., v_n)$,
we extend their domain to value results such that $f(v_1, ..., v_n)$ yields $v_i$
if $v_i$ is an exception and for all $j < i$, $v_j$ is a value.

A _stream_ (or lazy list) is written as $stream(v_0, ..., v_n)$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.
Given some stream $l = stream(x_0, ..., x_n)$, we write
$sum_(x in l) f(x)$ to denote $f(x_0) + ... + f(x_n)$.
We use this frequently to map a function over a stream,
by having $f(x)$ return a stream itself.

The following function $"head"(l, e)$ returns the head of a list $l$ if it is not empty, otherwise $e$:

$ "head"(l, e) := cases(
  h & "if" l = stream(h) + t,
  e & "otherwise",
) $


== Construction <construction>

In this subsection, we will introduce operators to construct arrays and objects.

The function $[dot]$ transforms a stream into
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

We can construct objects with multiple keys by adding objects, see @arithmetic.


== Simple functions <simple-fns>

We are now going to define several functions that take a value and return a value.

The _keys_ of a value are defined as follows:

$ "keys"(v) := cases(
  stream(0  , ...,   n) & "if" v = [v_0, ..., v_n],
  stream(k_0) + "keys"(v') & "if" v = {k_0 |-> v_0} union v' "and" k_0 = min("dom"(v)),
  stream() & "if" v = {},
  "error"         & "otherwise",
) $

For an object $v$, $"keys"(v)$ returns
the domain of the object sorted by ascending order.
For the used ordering, see @ordering.

We define the _length_ of a value as follows:

$ |v| := cases(
  0       & "if" v = "null",
  |n|     & "if" v "is a number" n,
  n       & "if" v = c_1...c_n,
  n       & "if" v = [v_1, ..., v_n],
  n       & "if" v = {k_1 |-> v_1, ..., k_n |-> v_n},
  "error" & "otherwise (if" v in {"true", "false"}")",
) $

The _boolean value_ of a value $v$ is defined as follows:

$ "bool"(v) := cases(
  "false" & "if" v = "null" "or" v = "false",
  "true" & "otherwise",
) $

We can draw a link between the functions here and jq:
When called with the input value $v$,
the jq filter `keys` yields $stream(["keys"(v)])$,
the jq filter `length` yields $stream(|v|)$, and
the jq filter `true and .` yields $stream("bool"(v))$.

== Arithmetic operations <arithmetic>

We define addition of two values $l$ and $r$ as follows:

$ l + r := cases(
  v & "if" l = "null" "and" r = v", or" l = v "and" r = "null",
  n_1 + n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  c_(l,1)...c_(l,m)c_(r,1)...c_(r,n) & "if" l = c_(l,1)...c_(l,m) "and" r = c_(r,1)...c_(r,n),
  [l_1, ..., l_m, r_1, ..., r_n] & "if" l = [l_1, ..., l_m] "and" r = [r_1, ..., r_n],
  l union r & "if" l = {...} "and" r = {...},
  "error" & "otherwise",
) $

Here, we can see that $"null"$ serves as a neutral element for addition.
For strings and arrays, addition corresponds to their concatenation, and
for objects, it corresponds to their union.

#let merge = $union.double$
Given two objects $l$ and $r$, we define their _recursive merge_ $l merge r$ as:

$ l merge r := cases(
  {k |-> v_l merge v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l"," v_r "are objects",
  {k |-> v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l "or" v_r "is not an object",
  {k |-> v_r} union l merge r' & "if" k in.not "dom"(l) "and" r = {k |-> v_r} union r',
  l & "otherwise (if" r = {} ")",
) $

We use this in the following definition of multiplication of two values $l$ and $r$:

$ l times r := cases(
  l + l times (r - 1) & "if" l "is a string and" r in bb(N) without {0},
  "null" & "if" l "is a string and" r = 0,
  r times l & "if" r "is a string and" l in bb(N),
  l times r & "if" l "and" r "are numbers",
  l merge r & "if" l "and" r "are objects",
  "error" & "otherwise"
) $

We can see that multiplication of a string $s$ with a natural number $n > 0$ returns
$sum_(i = 1)^n s$; that is, the concatenation of $n$ times the string $s$.
The multiplication of two objects corresponds to their recursive merge as defined above.

For two values $l$ and $r$, the arithmetic operations
$l - r$, $l div r$, and $l mod r$ (modulo) yield
$m - n$, $m div n$, and $m mod n$ if $l$ and $r$ are numbers $m$ and $n$,
otherwise they yield an error.

Suppose that the jq filters
`f` and `g` yield $stream(l)$ and $stream(r)$, respectively.
Then the jq filters `f + g` and `f * g` yield
$stream(l + r)$ and $stream(l times r)$, respectively.


== Accessing <accessing>

We will now define three _access operators_.
These serve to extract values that are contained within other values.

The value $v[i]$ of a value $v$ at index $i$ is defined as follows:

$ v[i] := cases(
  v_i    & "if" v = [v_0, ..., v_n] "," i in bb(N)", and" i <= n,
  "null" & "if" v = [v_0, ..., v_n] "," i in bb(N)", and" i > n,
  v[n+i] & "if" v = [v_0, ..., v_n] "," i in bb(Z) without bb(N)", and" 0 <= n+i,
  v_j    & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" k_j = i,
  "null" & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" i in.not {k_0, ..., k_n},
  "error" & "otherwise",
) $

The idea behind this index operator is as follows:
It returns $"null"$ if
the value $v$ does not contain a value at index $i$,
but $v$ could be _extended_ to contain one.
More formally, $v[i]$ is $"null"$ if $v != "null"$ and
there exists some value $v' = v + delta$ such that $v'[i] != "null"$.

The behaviour of this operator for $i < 0$ is that $v[i]$ equals $v[abs(v) + i]$.

#example[
  If $v = [0, 1, 2]$, then $v[1] = 1$ and $v[-1] = v[3 - 1] = 2$.
]

Using the index operator, we can define the values $v[]$ in a value $v$ as follows:

$ v[] := sum_(i in"keys"(v)) stream(v[i]) $

When provided with
an array $v = [v_0, ..., v_n]$ or
an object $v = {k_0 |-> v_0, ..., k_n |-> v_n}$ (where $k_0 < ... < k_n$),
$v[]$ returns the stream $stream(v_0, ..., v_n)$.

The last operator that we define here is a slice operator:

$ v[i:j] := cases(
  [sum_(k = i)^(j-1) stream(v_k)] & "if" v = [v_0, ..., v_n] "and" i","j in bb(N),
  sum_(k = i)^(j-1) c_k & "if" v = c_0...c_n "and" i","j in bb(N),
  v[(n+i):j] & "if" |v| = n", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v[i:(n+j)] & "if" |v| = n", " j in bb(Z) without bb(N)", and" 0 <= n+j,
  "error" & "otherwise",
) $

Note that unlike $v[]$ and $v[i]$, $v[i:j]$ may yield a value if $v$ is a string.
If we have that $i, j in bb(N)$ and either $i > n$ or $i >= j$, then $v[i:j]$ yields
an empty array  if $v$ is an array, and
an empty string if $v$ is a string.

#example[
  If $v = [0, 1, 2, 3]$, then $v[1:3] = [1, 2]$.
]

The operator $v[]$ is the only operator in this subsection that
returns a _stream_ of value results instead of only a value result.

== Updating

For each access operator in @accessing, we will now define an _updating_ counterpart.
Intuitively, where an access operator yields some elements contained in a value $v$,
its corresponding update operator _replaces_ these elements in $v$ by the output of a function.

All update operators take at least
a value $v$ and
a function $f$ from a value to a stream of value results.
We extend the domain of $f$ to value results such that
$f(e) = stream(e)$ if $e$ is an error.

The first update operator will be a counterpart to $v[]$.
For _all_ elements $x$ that are yielded by $v[]$,
$v[] update f$ replaces $x$ by $f(x)$:

$ v[] update f = cases(
  [sum_i f(v_i)] & "if" v = [v_0, ..., v_n],
  union.big_i cases({k_i : h} & "if" f(v_i) = stream(h) + t, {} & "otherwise") & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n},
  "error" & "otherwise",
) $

For an input array $v = [v_0, ..., v_n]$,
$v[] update f$ replaces each $v_i$ by the output of $f(v_i)$, yielding
$[f(v_0) + ... + f(v_n)]$.
For an input object $v = {k_0 |-> v_0, ..., k_n |-> v_n}$,
$v[] update f$ replaces each $v_i$ by the first output yielded by $f(v_i)$ if such an output exists,
otherwise it deletes ${k_i |-> v_i}$ from the object.
Note that updating arrays diverges from jq, because
jq only considers the first value yielded by $f$.

The next function takes a value $v$ and
replaces its $i$-th element by the first output of $f$,
or deletes it if $f$ yields no output:
$ v[i] update f = cases(
  v[0:i] + ["head"(f(v[i]), stream())] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in bb(N)", and" i <= n,
  /*
  v[0:i] + [h] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in bb(N)"," i <= n", and" f(v[i]) = stream(h) + t,
  v[0:i] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in bb(N)"," i <= n", and" f(v[i]) = stream(),
  */
  v[n+i] update f & "if" v = [v_0, ..., v_n]", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v + {i: h} & "if" v = {...} "and" f(v[i]) = stream(h) + t,
  union.big_(k in "dom"(v) without {i}) {k |-> v[k]} & "if" v = {...} "and" f(v[i]) = stream(),

  "error" & "otherwise",
) $

Note that this diverges from jq if $v = [v_0, ..., v_n]$ and $i > n$,
because jq fills up the array with $"null"$.

// but we unfortunately cannot use it to define {k: f}, because if f returns the empty list,
// we cannot provide a default element e that would make the key disappear

$ v[i:j] update f = cases(
  v[0:i] + "head"(f(v[i:j]), []) + v[j:n] & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i <= j,
  v & "if" v = [v_0, ..., v_n]", " i","j in bb(N)", and" i > j,
  v[(n+i):j] update f & "if" |v| = n", " i in bb(Z) without bb(N)", and" 0 <= n+i,
  v[i:(n+j)] update f & "if" |v| = n", " j in bb(Z) without bb(N)", and" 0 <= n+j,
  "error" & "otherwise",
) $

Unlike $v[i:j]$, this operator fails when $v$ is a string.

#example[
  If $v = [0, 1, 2, 3]$ and $f(v) = [4, 5, 6]$, then $v[1:3] update f = [0, 4, 5, 6, 3]$.
]

== Ordering <ordering>

In this subsection, we establish a total order on values.#footnote[
  Note that jq does _not_ implement a _strict_ total order on values;
  in particular, its order on (floating-point) numbers specifies $"nan" < "nan"$,
  from which follows that $"nan" != "nan"$ and $"nan" gt.not "nan"$.
]

We have that
$ "null" < "false" < "true" < n < s < a < o, $ where
$n$ is a number,
$s$ is a string,
$a$ is an array, and
$o$ is an object.
We assume that there is a total order on numbers and characters.
Strings and arrays are ordered lexicographically.

Two objects $o_1$ and $o_2$ are ordered as follows:
For both objects $o_i$ ($i in {1, 2}$),
we sort the array $["keys"(o_i)]$ by ascending order to obtain the ordered array of keys
$k_i = [k_1, ..., k_n]$, from which we obtain
$v_i = [o[k_1], ..., o[k_n]]$.
We then have $ o_1 < o_2 <==> cases(
  k_1 < k_2 & "if" k_1 < k_2 "or" k_1 > k_2,
  v_1 < v_2 & "otherwise" (k_1 = k_2)
) $

#example[
  TODO: For object comparison.
]



= Evaluation Semantics <semantics>

In this section, we will define a function $phi|^c_v$ that returns
the output of the evaluation of the filter $phi$ on the input value $v$.

Let us start with a few definitions.
A context $c$ is a mapping
from variables $var(x)$ to values and
from identifiers $x$ to pairs $(f, c)$, where $f$ is a filter and $c$ is a context.
Contexts store what variables and filter arguments are bound to.

We are now going to introduce a few helper functions.
The first function helps define filters such as if-then-else and alternation ($f alt g$):
$ "ite"(v, i, t, e) = cases(
  t & "if" v = i,
  e & "otherwise"
) $

We use the newly defined $"ite"$ function for another function that
we will use to define conjunction and disjunction:

If the boolean value of $x$ is $v$ (where $v$ will be true or false), then
$"junction"(x, v, l)$ returns just $v$, otherwise the boolean values of the values in $l$.
Here, $"bool"(v)$ returns the boolean value as given in @simple-fns.

$ "junction"(x, v, l) := "ite"("bool"(x), v, stream(v), sum_(y in l) stream("bool"(y))) $

Next, we define a function that is used to define alternation.
$"trues"(l)$ returns those elements of $l$ whose boolean values are not false.
Note that in our context, "not false" is _not_ the same as "true", because
the former includes exceptions, whereas the latter excludes them,
and $"bool"(x)$ _can_ return exceptions, in particular if $x$ is an exception.

$ "trues"(l) := sum_(x in l, "bool"(x) != "false") stream(x) $

The last helper function will be used to define the behaviour of label-break expressions.
$"label"(l, var(x))$ returns all elements of $l$ until
the current element is an exception of the form $"break"(var(x), v)$,
where $v$ is arbitrary.

$ "label"(l, var(x)) := cases(
  stream(h) + "label"(t, var(x)) & "if" l = stream(h) + t "and" h != "break"(var(x), v),
  stream() & "otherwise",
) $

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $phi|^c_v$,
  $.$, $stream(v)$,
  $n "or" s$, $stream(phi)$,
  $var(x)$, $stream(c(var(x)))$,
  $[f]$, $stream([f|^c_v])$,
  ${}$, $stream({})$,
  ${var(x): var(y)}$, ${c(var(x)): c(var(y))}$,
  $f, g$, $f|^c_v + g|^c_v$,
  $f | g$, $sum_(x in f|^c_v) g|^c_x$,
  $f alt g$, $"ite"("trues"(f|^c_v), stream(), g|^c_v, "trues"(f|^c_v))$,
  $f "as" var(x) | g$, $sum_(x in f|^c_v) g|^(c{var(x) |-> x})_v$,
  $var(x) cartesian var(y)$, $stream(c(var(x)) cartesian c(var(y)))$,
  $"try" f "catch" g$, $sum_(x in f|^c_v) cases(
    g|^c_e & "if" x = "error"(e),
    stream(x) & "otherwise"
  )$,
  $"label" var(x) | f$, $"label"(f|^c_v, var(x))$,
  $"break" var(x)$, $stream("break"(var(x), v))$,
  $var(x) "and" f$, $"junction"(c(var(x)), "false", f|^c_v)$,
  $var(x) "or"  f$, $"junction"(c(var(x)), "true" , f|^c_v)$,
  $"if" var(x) "then" f "else" g$, $"ite"("bool"(c(var(x))), "true", f|^c_v, g|^c_v)$,
  $.[]$, $v[]$,
  $.[var(x)]$, $stream(v[c(var(x))])$,
  $.[var(x):var(y)]$, $stream(v[c(var(x)):c(var(y))])$,
  $fold x "as" var(x) (var(y); f)$, $fold^c_c(var(y)) (x|^c_v, var(x), f)$,
  $x(f_1; ...; f_n)$, $g|^(c{x_1 |-> f_1, ..., x_n |-> f_n})_v "if" x(x_1; ...; x_n) := g$,
  $x$, $f|^c'_v "if" c(x) = (f, c')$,
  $f update g$, [see @updates]
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss the filters in detail:

- "$.$": Returns its input value. This is the identity filter.
- $n$ or $s$: Returns the value corresponding to the number $n$ or string $s$.
- $var(x)$: Returns the value currently bound to the variable $var(x)$,
  by looking it up in the context.
  Wellformedness of the filter (as defined in @hir) ensures that such a value always exists.
- $[f]$: Creates an array from the output of $f$, using the operator defined in @construction.
- ${}$: Creates an empty object.
- ${var(x): var(y)}$: Creates an object from the values bound to $var(x)$ and $var(y)$,
  using the operator defined in @construction.
- $f, g$: Concatenates the outputs of $f$ and $g$.
- $f | g$: Composes $f$ and $g$, returning the outputs of $g$ applied to all outputs of $f$.
- $f alt g$: Returns $l$ if $l$ is not empty, else the outputs of $g$, where
  $l$ are the outputs of $f$ whose boolean values are not false.
- $f "as" var(x) | g$: Binds every output of $f$ to the variable $var(x)$ and
  returns the output of $g$, where $g$ may reference $var(x)$.
  Unlike $f | g$, this runs $g$ with the original input value instead of an output of $f$.
- $var(x) cartesian var(y)$: Returns the output of a Cartesian operation "$cartesian$"
  (any of $eq.quest$, $eq.not$, $<$, $<=$, $>$, $>=$, $+$, $-$, $times$, $div$, and $mod$,
  as given in @tab:binops) on the values bound to $var(x)$ and $var(y)$.
  The semantics of the arithmetic operators are given in @arithmetic,
  the comparison operators are defined by the ordering given in @ordering,
  $l eq.quest r$ returns whether $l$ equals $r$, and
  $l eq.not r$ returns its negation.
- $"try" f "catch" g$: Returns the output of $f$ where
  all outputs $"error"(v)$ are replaced by the output of $g$ on the input $v$.
  Note that this diverges from jq, which aborts the evaluation of $f$ after the first error.
  This behaviour can be simulated in our semantics, by replacing
  $"try" f "catch" g$ with
  $"label" var(x') | "try" f "catch" (g, "break" var(x'))$.
- $"label" var(x) | f$: Returns all values yielded by $f$ until $f$ yields
  an exception $"break"(var(x), v)$ (where $v$ is arbitrary).
- $"break" var(x)$: Returns a value $"break"(var(x), v)$, where $v$ is the current input.
- $var(x) "and" f$: Returns false if $var(x)$ is bound to either null or false, else
  returns the output of $f$ mapped to boolean values.
- $var(x) "or" f$": Similar to its "and" counterpart above.
- $"if" var(x) "then" f "else" g$: Returns the output of $f$ if $var(x)$ is bound to either null or false, else returns the output of $g$.
- $.[]$, $.[var(x)]$, or $.[var(x):var(y)]$: Accesses parts of the input value; see @accessing for the definitions of the operators.
- $fold x "as" var(x) (var(y); f)$: Folds $f$ over the values returned by $x$,
  starting with the accumulator $var(y)$.
  The current accumulator value is provided to $f$ as input value and
  $f$ can access the current value of $x$ by $var(x)$.
  We will give a definition of the 
- TODO: function calls, updates

An implementation may also define custom semantics for named filters.
For example, an implementation may define
$"keys"|^c_v := "keys"(v)$ and
$"length"|^c_v := |v|$.
In the case of $"keys"$, for example, this is useful because
it would be extremely complicated to define this filter by definition.


== Folding

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

// TODO: clarify that "for" is not part of jq

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
// is $"foreach" x "as" var(x) (y_0; f)$ equivalent to $"foreach" x "as" var(x) (y_0; "first"(f))$ in the jq implementation?

Both filters fold $f$ over the sequence given by $x$ with the initial value $y_0$.
Their main difference is that "reduce" returns only the final value(s),
whereas "for" also returns all intermediate ones.

The following property can be used to eliminate bindings.

#lemma[
  Let $phi(f)$ be a filter such that $phi(f)|^c_v$ has the shape
  "$sum_(x in f|^c_v) ...$".
  Then $phi(f)$ is equivalent to "$f "as" var(x) | phi(var(x))$".
]

// TODO: remove some filter cases in proof of lemma --- it's not exhaustive anyway right now
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


== Object Construction

In @tab:lowering, we showed how to lower a HIR filter
${k_1: v_1, ..., k_n: v_n}$ into a sum of smaller filters
${k_1: v_1} + ... + {k_n: v_n}$.

From the lowering and the semantics defined in this section, we can conclude the following:
If $n > 0$, then $floor({k_1: v_1, ..., k_n: v_n})|^c_v$ is equivalent to
$ sum_(k_1 in floor(k_1)|^c_v) sum_(v_1 in floor(v_1)|^c_v) ... sum_(k_n in floor(k_n)|^c_v) sum_(v_n in floor(v_n)|^c_v)
stream({k_1: v_1} union ... union {k_n: v_n}). $

#example[
  The evaluation of
  ${qs(a): (1, 2), (qs(b), qs(c): 3, qs(d): 4}$
  //(with arbitrary context and input)
  yields $stream(v_0, v_1, v_2, v_3)$, where $
  v_0 = {qs(a) |-> 1, qs(b) |-> 3, qs(d) |-> 4},\
  v_1 = {qs(a) |-> 1, qs(c) |-> 3, qs(d) |-> 4},\
  v_2 = {qs(a) |-> 2, qs(b) |-> 3, qs(d) |-> 4},\
  v_3 = {qs(a) |-> 2, qs(c) |-> 3, qs(d) |-> 4}.
  $
]



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
  $.$, $sigma(v)$,
  $f | g$, $(f update sigma')|^c_v "where" sigma'(x) = (g update sigma)|^c_x$,
  $f, g$, $sum_(x in (f update sigma)|^c_v) (g update sigma)|^c_x$,
  $f alt g$, $"ite"("trues"(f|^c_v), stream(), (g update sigma)|^c_v, (f update sigma)|^c_v)$,
  $.[]$, $stream(v[] update sigma(v))$,
  $.[var(x)]$, $stream(v[c(var(x))] update sigma(v))$,
  $.[var(x):var(y)]$, $stream(v[c(var(x)):c(var(y))] update sigma(v))$,
  $f "as" var(x) | g$, $"reduce"^c_v (f|^c_v, var(x), (g update sigma))$,
  $"if" var(x) "then" f "else" g$, $"ite"(c(var(x)), "true", (f update sigma)|^c_v, (g update sigma)|^c_v)$,
  $"try" f "catch" g$, $sum_(x in (f update sigma)|^c_v) "catch"(x, g, c, v)$,
  $"label" var(x) | f$, $"label"(var(x), f update sigma)$,
  $"break" var(x)$, $stream(breakr(x, v))$,
  $x(f_1; ...; f_n)$, $(g update sigma)|^(c{x_1 |-> f_1, ..., x_n |-> f_n})_v "if" x(x_1; ...; x_n) := g$,
  $x$, $(f update sigma)|^c'_v "if" c(x) = (f, c')$,
)) <tab:update-semantics>

$ "label"(var(x), l) := cases(
  stream(v) & "if" l = stream(breakr(x, v)) + t,
  stream(h) + "label"(var(x), t) & "if" l = stream(h) + t "and" h != breakr(x, v),
  stream() & "if" l = stream(),
) $

$ "catch"(x, g, c, v) := cases(
    sum_(e in g|^c_(x)) stream("error"(e)) & "if" x "is an unpolarised error and" g|^c_x != stream(),
    stream(v) & "if" x "is an unpolarised error and" g|^c_x = stream(),
    stream(x) & "otherwise"
) $

#figure(caption: [Update semantics properties.], table(columns: 2,
  $mu$, $mu update sigma$,
  $"empty"$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $"if" var(x) "then" f "else" g$, $"if" var(x) "then" f update sigma "else" g update sigma$,
  $f alt g$, $"if" "first"(f alt "null") "then" f update sigma "else" g update sigma$,
)) <tab:update-props>

Here, we have that $"first"(f) := "label" var(x) | f | (., "break" var(x))$.
This filter returns the first output of $f$ if $f$ yields any output, else nothing.

For two filters $f$ and $g$, we define
$(f update g)|^c_v := sum_(y in (f update sigma)|^c_v) "depolarise"(y)$, where
$sigma(x) = sum_(y in g|^c_x) "polarise"(y)$.
The function "polarise" marks exceptions occurring in the filter $g$,
and "depolarise" removes the marker from exceptions.

The update semantics are given in @tab:update-semantics.

- $f alt g$: Updates using $f$ if $f$ yields some non-false value, else updates using $g$.
  Here, $f$ is called as a "probe" first.
  If it yields at least one output that is considered "true"
  (see @semantics for the definition of $"trues"$),
  then we update at $f$, else at $g$.
  This filter is unusual because is the only kind where a subexpression is both
  updated with ($(f update sigma)|^c_v$) and evaluated ($f|^c_v$).

#example("The Curious Case of Alternation")[
  The semantics of $(f alt g) update sigma$ can be rather surprising:
  For the input
  ${qs(a) |-> "true"}$, the filter
  $(oat(a) alt oat(b)) update 1$ yields
  ${qs(a) |-> 1}$.
  This is what we might expect, because the input has an entry for $qs(a)$.
  Now let us evaluate the same filter on the input
  ${qs(a) |-> "false"}$, which yields ${qs(a) |-> "false", qs(b) |-> 1}$.
  Here, while the input still has an entry for $qs(a)$ like above,
  its boolean value is _not_ true, so $oat(b) update 1$ is executed.
  In the same spirit, for the input ${}$ the filter yields ${qs(b) |-> 1}$,
  because $oat(a)$ yields $"null"$ for the input,
  which also has the boolean value $"false"$, therefore $oat(b) update 1$ is executed.

  For the input
  ${}$, the filter
  $("false" alt oat(b)) update 1$ yields
  ${qs(b) |-> 1}$.
  This is remarkable insofar as $"false"$ is not a valid path expression
  because it returns a value that does not refer to any part of the original input,
  yet the filter does not return an error.
  This is because
  $"false"$ triggers $oat(b) update 1$, so
  $"false"$ is never used as path expression.
  However, running the filter $("true" alt oat(b)) update 1$
  _does_ yield an error, because
  $"true"$ triggers $"true" update 1$, and
  $"true"$ is not a valid path expression.

  Finally, on the input
  $[]$, the filter
  $(.[] alt "error") update 1$ yields
  $"error"([])$.
  That is because $.[]$ does not yield any value for the input,
  so $"error" update 1$ is executed, which yields an error.
]

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
