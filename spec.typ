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
  anonymous: true,
  ccs: (
    ([Software and its engineering], (
      (500, [Semantics]),
      (500, [Functional languages]),
    )),
  ),
  abstract: [
    jq is a widely used tool that provides a programming language to manipulate JSON data.
    However, the jq language is currently only specified by its implementation,
    making it difficult to reason about its behaviour.
    To this end, we provide a formal syntax and denotational semantics for
    a large subset of the jq language.
    Our most significant contribution is to provide a new way to interpret updates
    that allows for more predictable and performant execution.
  ],
  keywords: ("jq", "JSON", "semantics"),

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

#let thm(x, y, ..args) = thmplain(x, y, inset: (left: 0em, right: 0em), ..args)
#let example = thm("example", "Example")
#let lemma = thm("theorem", "Lemma")
#let theorem = thm("theorem", "Theorem")
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

#let qs(s) = $quote #s quote$
#let oat(k) = $.[#qs(k)]$

/*
TODO:
- completeness is if we can construct any valid value
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
the number of streets (6528) with the filter "`length`",
the names of the streets with the filter "`.[].nomvoie`", and
the total length of all streets (1574028 m) with the filter "`[.[].longueur] | add`".
jq provides syntax to update data; for example,
to remove geographical data obtained by
"`.[].geo_shape`", but leaving intact all other data, we can use
"`.[].geo_shape |= empty`".
// jq -c was used for both formatting the original dataset and the "shrunk" one.
This shrinks the dataset from \~25 MB to \~7 MB.
jq provides a Turing-complete language that is interesting on its own; for example,
"`[0, 1] | recurse([.[1], add])[0]"` generates the stream of Fibonacci numbers.
This makes jq a widely used tool.
We refer to the program jq as "jq" and to its language as "the jq language".

The jq language is a dynamically typed, lazily evaluated
functional programming language with
second-class higher-order functions @jq-description.
The semantics of the jq language are only
informally specified, for example in the jq manual @jq-manual.
However, the documentation frequently does not cover certain cases, and
historically, the implementation often contradicted the documentation.
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
Therefore, we have striven to create
denotational semantics (@semantics) that closely resemble those of jq such that
in most cases, their behaviour coincides, whereas they may differ in more exotic cases.
The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe, understand, and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.

We created these semantics experimentally, by coming up with
jq filters and observing their output for all kinds of inputs.
From this, we synthesised mathematical definitions to model the behaviour of jq.
The most significant improvement over jq behaviour described in this text are
the new update semantics (@updates), which
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
The semantics of jq and those that will be shown in this text
differ most notably in the case of updates.
Finally, we show how to prove properties of jq programs by equational reasoning in @obj-eq.

#figure(caption: [Evaluation of a jq program with an input value.
  Solid lines indicate data flow, whereas a dashed line indicates that
  a component is defined in terms of another.
], diagraph.render(read("structure.dot"))) <fig:structure>



= Tour of jq <tour>

This goal of this section is to convey an intuition about how jq functions.
The official documentation of jq is @jq-manual.

jq programs are called _filters_.
For now, let us consider a filter to be a function from a value to
a (lazy, possibly infinite) stream of values.
Furthermore, in this section, let us assume a value to be either
a boolean, an integer, or an array of values.
(We introduce the full set of JSON values in @values.)

The identity filter "`.`" returns a stream containing the input.#footnote[
  The filters in this section can be executed on most UNIX shells by
  `echo $INPUT | jq $FILTER`, where
  `$INPUT` is the input value in JSON format and
  `$FILTER` is the jq program to be executed.
  Often, it is convenient to quote the filter; for example,
  to run the filter "`.`" with the input value `0`,
  we can run `echo 0 | jq '.'`.
  In case where the input value does not matter,
  we can also use `jq -n $FILTER`,
  which runs the filter with the input value `null`.
  We use jq 1.7.
]

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
  jq defines a filter "`in(xs)`" that expands to "`. as $x | xs | has($x)`".
  Given an input value `i`, "`in(xs)`" binds it to `$x`, then returns
  for every value produced by `xs` whether its domain contains `$x` (and thus `i`).
  Here, the domain of an array is the set of its indices.
  For example, for the input
  `1`, the filter
  "`in([5], [42, 3], [])`" yields the stream
  `false, true, false`,
  because only `[42, 3]` has a length greater than 1 and thus a domain that contains `1`.
  The point of this example is that
  we wish to pass `xs` as input to `has`, but at the same point,
  we also want to pass the input given to `in` as an argument to `has`.
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
#cite(label("DBLP:conf/icfp/FosterPP08"))
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
"`.[] |= f`" being equivalent to "`[.[] | f]`" when the input value is an array, or
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
We will show such semantics in @updates.



= Syntax <syntax>

This section describes the syntax for a subset of the jq language
that will be used later to define the semantics in @semantics.
To set the formal syntax apart from
the concrete syntax introduced in @tour,
we use cursive font (as in "$f$", "$v$") for the specification
instead of the previously used typewriter font (as in "`f`", "`v`").

We will start by introducing high-level intermediate representation (HIR) syntax in @hir.
This syntax is very close to actual jq syntax.
Then, we will identify a subset of HIR as mid-level intermediate representation (MIR) in @mir
and provide a way to translate from HIR to MIR.
This will simplify our semantics in @semantics.
Finally, in @jq-syntax, we will show how HIR relates to actual jq syntax.

== HIR <hir>

A _filter_ $f$ is defined by

$ f :=& n #or_ s #or_ . \
  #or_& (f) #or_ f? #or_ [f] #or_ {f: f, ..., f: f} #or_ f p^? ... p^? \
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
We use the superscript "$?$" to denote an optional presence of "?"; in particular,
$f p^?... p^?$ can be
$f p$, $f p?$,
$f p p$, $f p?#h(0pt) p$, $f p p?$, $f p?#h(0pt) p?$,
$f p p p$, and so on.
The potential instances of the operators $star$ and $cartesian$ are given in @tab:binops.
All operators $star$ and $cartesian$ are left-associative, except for
"$|$", "$=$", "$update$", and "$aritheq$".
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

A _filter definition_ has the shape
"$f(x_1; ...; x_n) := g$".
Here, $f$ is an $n$-ary filter with _filter arguments_ $x_i$, where $g$ may refer to $x_i$.
For example, this allows us to define filters that produce the booleans,
by defining $"true()" := (0 = 0)$ and $"false()" := (0 != 0)$.

// TODO: these must also hold for the main filter!
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
  #or_& [f] #or_ {} #or_ {f: f} #or_ .p \
  #or_& f star f #or_ var(x) cartesian var(x) \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (.; f) #or_ var(x) \
  #or_& "if" var(x) "then" f "else" f #or_ "try" f "catch" f \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& x #or_ x(f; ...; f)
$
where $p$ is a path part of the shape
$ p := [] #or_ [var(x)] #or_ [var(x):var(x)]. $
Furthermore, the set of complex operators $star$ in MIR
does not include "$=$" and "$aritheq$" anymore.

Compared to HIR, MIR filters
have significantly simpler path operations
($.p$ versus $f p^?... p^?$) and
replace certain occurrences of filters by variables
(e.g. $var(x) cartesian var(x)$ versus $f cartesian f$).

#figure(caption: [Lowering of a	HIR filter $phi$ to a MIR filter $floor(phi)$.], table(columns: 2,
  $phi$, $floor(phi)$,
  [$n$, $s$, $.$, $var(x)$, or $"break" var(x)$], $phi$,
  $(f)$, $floor(f)$,
  $f?$, $"try" floor(f) "catch" "empty"()$,
  $[]$, $["empty"()]$,
  $[f]$, $[floor(f)]$,
  ${}$, ${}$,
  ${f: g}$, $floor(f) "as" var(x') | floor(g) "as" var(y') | {var(x'): var(y')}$,
  ${f_1: g_1, ..., f_n: g_n}$, $floor(sum_i {f_i: g_i})$,
  $f p_1^? ... p_n^?$, $. "as" var(x') | floor(f) | floor(p_1^?)_var(x') | ... | floor(p_n^?)_var(x')$,
  $f = g$, $floor(g) "as" var(x') | floor(f update var(x'))$,
  $f aritheq g$, $floor(f update . arith g)$,
  $f alteq g$, $floor(f update . alt g)$,
  $f "and" g$, $floor(f) "as" var(x') | var(x') "and" floor(g)$,
  $f "or"  g$, $floor(f) "as" var(x') | var(x') "or"  floor(g)$,
  $f star g$, $floor(f) star floor(g)$,
  $f cartesian g$, $floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
  $f "as" var(x) | g$, $floor(f) "as" var(x) | floor(g)$,
  $fold f_x "as" var(x) (f_y; f)$, $. "as" var(x') | floor(f_y) | fold floor(var(x') | f_x) "as" var(x) (.; floor(f))$,
  $"if" f_x "then" f "else" g$, $floor(f_x) "as" var(x') | "if" var(x') "then" floor(f) "else" floor(g)$,
  $"try" f "catch" g$, $"try" floor(f) "catch" floor(g)$,
  $"label" var(x) | f$, $"label" var(x) | floor(f)$,
  $x$, $x$,
  $x(f_1; ...; f_n)$, $x(floor(f_1); ...; floor(f_n))$,
)) <tab:lowering>

@tab:lowering shows how to lower an HIR filter $phi$ to
a semantically equivalent MIR filter $floor(phi)$.
In particular, this desugars path operations and
makes it explicit which operations are Cartesian or complex.
By convention, we write $var(x')$ to denote a fresh variable.
Notice that for some complex operators $star$, namely
"$=$", "$aritheq$", "$alteq$", "$"and"$", and "$"or"$",
@tab:lowering specifies individual lowerings, whereas
for the remaining complex operators $star$, namely
"$|$", "$,$", "$update$", and "$alt$",
@tab:lowering specifies a uniform lowering $floor(f star g) = floor(f) star floor(g)$.

#figure(caption: [Lowering of a path part $p^?$ with input $var(x)$ to a MIR filter.], table(columns: 2, align: left,
  $p    ^?$, $floor(p^?)_var(x)$,
  $[   ]^?$, $.[]^?$,
  $[f  ]^?$, $(var(x) | floor(f)) "as" var(y') | .[var(y')]^?$,
  $[f: ]^?$, $(var(x) | floor(f)) "as" var(y') | "length"()^? "as" var(z') | .[var(y') : var(z')]^?$,
  $[ :f]^?$, $(var(x) | floor(f)) "as" var(y') | 0 "as" var(z') | .[var(z') : var(y')]^?$,
  $[f:g]^?$, $(var(x) | floor(f)) "as" var(y') | (var(x) | floor(g)) "as" var(z') | .[var(y') : var(z')]^?$,
)) <tab:lower-path>

@tab:lower-path shows how to lower a path part $p^?$ to MIR filters.
Like in @hir, the meaning of superscript "$?$" is an optional presence of "$?$".
In the lowering of $f p_1^? ... p_n^?$ in @tab:lowering,
if $p_i$ in the first column is directly followed by "?", then
$floor(p_i^?)_var(x)$ in the second column stands for
$floor(p_i ?#h(0pt))_var(x)$, otherwise for
$floor(p_i  )_var(x)$.
Similarly, in @tab:lower-path, if $p$ in the first column is followed by "$?$", then
all occurrences of superscript "?" in the second column stand for "?", otherwise for nothing.

#example[
  The HIR filter $(.[]?#h(0pt) [])$ is lowered to
  $(. "as" var(x') | . | .[]? | .[])$.
  Semantically, we will see that this is equivalent to $(.[]? | .[])$.
]

#example[
  The HIR filter $mu eq.triple .[0]$ is lowered to
  $floor(mu) eq.triple . "as" var(x) | . | (var(x) | 0) "as" var(y) | .[var(y)]$.
  Semantically, we will see that $floor(mu)$ is equivalent to $0 "as" var(y) | .[var(y)]$.
  The HIR filter $phi eq.triple [3] | .[0] = ("length"(), 2)$ is lowered to the MIR filter
  $floor(phi) eq.triple [3] | ("length"(), 2) "as" var(z) | floor(mu) update var(z)$.
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
$ "empty"() := ({} | .[]) "as" var(x) | . $
This definition ensures that $"empty"$ can be employed also as a path expression.

The lowering in @tab:lowering is compatible with the semantics of the jq implementation,
with one notable exception:
In jq, Cartesian operations $f cartesian g$ would be lowered to
$floor(g) "as" var(y') | floor(f) "as" var(x') | var(x) cartesian var(y)$, whereas we lower it to
$floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
thus inverting the binding order.
Note that the difference only shows when both $f$ and $g$ return multiple values.
We diverge here from jq to make the lowering of Cartesian operations
consistent with that of other operators, such as ${f: g}$, where
the leftmost filter ($f$) is bound first and the rightmost filter ($g$) is bound last.
That also makes it easier to describe other filters, such as
${f_1: g_1, ..., f_n: g_n}$, which we can lower to
$floor(sum_i {f_i: g_i})$, whereas its lowering assuming the jq lowering of Cartesian operations would be
$floor({f_1: g_1}) "as" var(x'_1) | ... | floor({f_n: g_n}) "as" var(x'_n) | sum_i var(x'_i)$.

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

A _program_ is a (possibly empty) sequence of definitions, followed by
a _main filter_ `f`.
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

In jq, it is invalid syntax to
call a nullary filter as `x()` instead of `x`, or to
define a nullary filter as `def x(): f;` instead of `def x: f;`.
On the other hand, on the right-hand side of a definition, `x` may refer either to
a filter argument `x` or a nullary filter `x`.
To ease our lives when defining the semantics, we allow the syntax $x()$ in HIR.
We unambiguously interpret $x$ as call to a filter argument and
$x()$ as call to a filter that was defined as $x() := f$.

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
+ Convert the main filter `f` to a HIR filter $f$.
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
  $"select"(f) := "if" f "then" . "else" "empty"()$ and
  $"negative"() := . < 0$, and
  the main filter is converted to the HIR filter
  $.[] | "select"("negative"())$.
  Both the definition of $"select"(f)$ and the main filter are already in MIR;
  the MIR version of the remaining definition is
  $"negative"() := . "as" var(x') | 0 "as" var(y') | var(x') < var(y')$.
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
  ${k_0: v_0, ..., k_n: v_n}$ syntax to denote the _construction_ of objects, and use
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
We will sometimes write arrays as $[v_0, ..., v_n]$ and sometimes as $[v_1, ..., v_n]$:
The former case is useful to express that $n$ is the maximal index of the array (having length $n+1$), and
the latter case is useful to express that the array has length $n$.
The same idea applies also to strings, objects, and streams.

A number can be an integer or a decimal, optionally followed by an integer exponent.
For example, $0$, $-42$, $3.14$, $3 times 10^8$ are valid JSON numbers.
This text does not fix how numbers are to be represented,
just like the JSON standard does not impose any representation.#footnote[
  jq uses floating-point numbers to encode both integers and decimals.
  However, several operations in this text (for example those in @accessing)
  make only sense for natural numbers $NN$ or integers $ZZ$.
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

An _exception_ either is an error or has the shape $"break"(var(x))$.
The latter will become relevant starting from @semantics.

A _value result_ is either a value or an exception.

A _stream_ (or lazy list) is written as $stream(v_0, ..., v_n)$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.
Given some stream $l = stream(x_0, ..., x_n)$, we write
$sum_(x in l) f(x)$ to denote $f(x_0) + ... + f(x_n)$.
We use this frequently to map a function over a stream,
by having $f(x)$ return a stream itself.

In this text, we will see many functions that take values as arguments.
By convention, for any of these functions $f(v_1, ..., v_n)$,
we extend their domain to value results such that $f(v_1, ..., v_n)$ yields $v_i$
(or rather $stream(v_i)$ if $f$ returns streams)
if $v_i$ is an exception and for all $j < i$, $v_j$ is a value.
For example, in @arithmetic, we will define $l + r$ for values $l$ and $r$,
and by our convention, we extend the domain of addition to value results such that
if $l$ is an exception, then $l + r$ returns just $l$, and
if $l$ is a value, but $r$ is an exception, then $l + r$ returns just $r$.



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
  stream("error") & "otherwise",
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
  n_1 times n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  l + l times (r - 1) & "if" l "is a string and" r in NN without {0},
  "null" & "if" l "is a string and" r = 0,
  r times l & "if" r "is a string and" l in NN,
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
  v_i    & "if" v = [v_0, ..., v_n] "," i in NN", and" i <= n,
  "null" & "if" v = [v_0, ..., v_n] "," i in NN", and" i > n,
  v[n+i] & "if" v = [v_0, ..., v_n] "," i in ZZ without NN", and" 0 <= n+i,
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
  [sum_(k = i)^(j-1) stream(v_k)] & "if" v = [v_0, ..., v_n] "and" i","j in NN,
  sum_(k = i)^(j-1) c_k & "if" v = c_0...c_n "and" i","j in NN,
  v[(n+i):j] & "if" |v| = n", " i in ZZ without NN", and" 0 <= n+i,
  v[i:(n+j)] & "if" |v| = n", " j in ZZ without NN", and" 0 <= n+j,
  "error" & "otherwise",
) $

Note that unlike $v[]$ and $v[i]$, $v[i:j]$ may yield a value if $v$ is a string.
If we have that $i, j in NN$ and either $i > n$ or $i >= j$, then $v[i:j]$ yields
an empty array  if $v$ is an array, and
an empty string if $v$ is a string.

#example[
  If $v = [0, 1, 2, 3]$, then $v[1:3] = [1, 2]$.
]

The operator $v[]$ is the only operator in this subsection that
returns a _stream_ of value results instead of only a value result.


== Updating <updating>

For each access operator in @accessing, we will now define an _updating_ counterpart.
Intuitively, where an access operator yields some elements contained in a value $v$,
its corresponding update operator _replaces_ these elements in $v$
by the output of a function.
The access operators will be used in @semantics, and
the update operators will be used in @updates.

All update operators take at least
a value $v$ and
a function $f$ from a value to a stream of value results.
We extend the domain of $f$ to value results such that
$f(e) = stream(e)$ if $e$ is an exception.

The first update operator will be a counterpart to $v[]$.
For all elements $x$ that are yielded by $v[]$,
$v[] update f$ replaces $x$ by $f(x)$:

$ v[] update f := cases(
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

For the next operators, we will use the following function $"head"(l, e)$, which
returns the head of a list $l$ if it is not empty, otherwise $e$:

$ "head"(l, e) := cases(
  h & "if" l = stream(h) + t,
  e & "otherwise",
) $

The next function takes a value $v$ and
replaces its $i$-th element by the first output of $f$,
or deletes it if $f$ yields no output:
$ v[i] update f := cases(
  v[0:i] + ["head"(f(v[i]), stream())] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN", and" i <= n,
  /*
  v[0:i] + [h] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN"," i <= n", and" f(v[i]) = stream(h) + t,
  v[0:i] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN"," i <= n", and" f(v[i]) = stream(),
  */
  v[n+i] update f & "if" v = [v_0, ..., v_n]", " i in ZZ without NN", and" 0 <= n+i,
  v + {i: h} & "if" v = {...} "and" f(v[i]) = stream(h) + t,
  union.big_(k in "dom"(v) without {i}) {k |-> v[k]} & "if" v = {...} "and" f(v[i]) = stream(),

  "error" & "otherwise",
) $

Note that this diverges from jq if $v = [v_0, ..., v_n]$ and $i > n$,
because jq fills up the array with $"null"$.

// but we unfortunately cannot use it to define {k: f}, because if f returns the empty list,
// we cannot provide a default element e that would make the key disappear

The final function here is the update counterpart of the operator $v[i:j]$.
It replaces the slice $v[i:j]$
by the first output of $f$ on $v[i:j]$, or
by the empty array if $f$ yields no output.
$ v[i:j] update f := cases(
  v[0:i] + "head"(f(v[i:j]), []) + v[j:n] & "if" v = [v_0, ..., v_n]", " i","j in NN", and" i <= j,
  v & "if" v = [v_0, ..., v_n]", " i","j in NN", and" i > j,
  v[(n+i):j] update f & "if" |v| = n", " i in ZZ without NN", and" 0 <= n+i,
  v[i:(n+j)] update f & "if" |v| = n", " j in ZZ without NN", and" 0 <= n+j,
  "error" & "otherwise",
) $

Unlike its corresponding access operator $v[i:j]$,
this operator unconditionally fails when $v$ is a string.
This operator diverges from jq if $f$ yields $"null"$, in which case
jq returns an error, whereas
this operator treats this as equivalent to $f$ returning $[]$.

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



= Evaluation Semantics <semantics>

In this section, we will define a function $phi|^c_v$ that returns
the output of the filter $phi$ in the context $c$ on the input value $v$.

Let us start with a few definitions.
A _context_ $c$ is a mapping
from variables $var(x)$ to values and
from identifiers $x$ to pairs $(f, c)$, where $f$ is a filter and $c$ is a context.
Contexts store what variables and filter arguments are bound to.

We are now going to introduce a few helper functions.
The first function helps define filters such as if-then-else and alternation ($f alt g$):
$ "ite"(v, i, t, e) = cases(
  t & "if" v = i,
  e & "otherwise"
) $

Next, we define a function that is used to define alternation.
$"trues"(l)$ returns those elements of $l$ whose boolean values are not false.
Note that in our context, "not false" is _not_ the same as "true", because
the former includes exceptions, whereas the latter excludes them,
and $"bool"(x)$ _can_ return exceptions, in particular if $x$ is an exception.

$ "trues"(l) := sum_(x in l, "bool"(x) != "false") stream(x) $

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $phi|^c_v$,
  $.$, $stream(v)$,
  $n "or" s$, $stream(phi)$,
  $var(x)$, $stream(c(var(x)))$,
  $[f]$, $stream([f|^c_v])$,
  ${}$, $stream({})$,
  ${var(x): var(y)}$, $stream({c(var(x)): c(var(y))})$,
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
  $"break" var(x)$, $stream("break"(var(x)))$,
  $var(x) "and" f$, $"junction"(c(var(x)), "false", f|^c_v)$,
  $var(x) "or"  f$, $"junction"(c(var(x)), "true" , f|^c_v)$,
  $"if" var(x) "then" f "else" g$, $"ite"("bool"(c(var(x))), "true", f|^c_v, g|^c_v)$,
  $.[]$, $v[]$,
  $.[var(x)]$, $stream(v[c(var(x))])$,
  $.[var(x):var(y)]$, $stream(v[c(var(x)):c(var(y))])$,
  $fold x "as" var(x) (.; f)$, $fold^c_v (x|^c_v, var(x), f)$,
  $x(f_1; ...; f_n)$, $f|^(c union union.big_i {x_i |-> (f_i, c)})_v "if" x(x_1; ...; x_n) := f$,
  $x$, $f|^c'_v "if" c(x) = (f, c')$,
  $f update g$, [see @updates]
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss its different cases:

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
- $f "as" var(x) | g$: For every output of $f$, binds it to the variable $var(x)$ and
  returns the output of $g$, where $g$ may reference $var(x)$.
  Unlike $f | g$, this runs $g$ with the original input value instead of an output of $f$.
  We can show that the evaluation of $f | g$ is equivalent to that of
  $f "as" var(x') | var(x') | g$, where $var(x')$ is a fresh variable.
  Therefore, we could be tempted to lower $f | g$ to
  $floor(f) "as" var(x') | var(x') | floor(g)$ in @tab:lowering.
  However, we cannot do this because we will see in @updates that
  this equivalence does _not_ hold for updates; that is,
  $(f | g) update sigma$ is _not_ equal to $(f "as" var(x') | var(x') | g) update sigma$.
- $var(x) cartesian var(y)$: Returns the output of a Cartesian operation "$cartesian$"
  (any of $eq.quest$, $eq.not$, $<$, $<=$, $>$, $>=$, $+$, $-$, $times$, $div$, and $mod$,
  as given in @tab:binops) on the values bound to $var(x)$ and $var(y)$.
  The semantics of the arithmetic operators are given in @arithmetic,
  the comparison operators are defined by the ordering given in @ordering,
  $l eq.quest r$ returns whether $l$ equals $r$, and
  $l eq.not r$ returns its negation.
- $"try" f "catch" g$: Replaces all outputs of $f$ that equal $"error"(e)$ for some $e$
  by the output of $g$ on the input $e$.
  Note that this diverges from jq, which aborts the evaluation of $f$ after the first error.
  This behaviour can be simulated in our semantics, by replacing
  $"try" f "catch" g$ with
  $"label" var(x') | "try" f "catch" (g, "break" var(x'))$.
- $"label" var(x) | f$: Returns all values yielded by $f$ until $f$ yields
  an exception $"break"(var(x))$.
  This uses the function $"label"(l, var(x))$, which returns all elements of $l$ until
  the current element is an exception of the form $"break"(var(x))$:
  $ "label"(l, var(x)) := cases(
    stream(h) + "label"(t, var(x)) & "if" l = stream(h) + t "and" h != "break"(var(x)),
    stream() & "otherwise",
  ) $
- $"break" var(x)$: Returns a value $"break"(var(x))$.
  Similarly to the evaluation of variables $var(x)$ described above,
  wellformedness of the filter (as defined in @hir) ensures that
  the returned value $"break"(var(x))$ will be
  eventually handled by a corresponding filter
  $"label" var(x) | f$.
  That means that the evaluation of a wellformed filter can only yield
  values and errors, but never $"break"(var(x))$.
- $var(x) "and" f$: Returns false if $var(x)$ is bound to either null or false, else
  returns the output of $f$ mapped to boolean values.
  This uses the function $"junction"(x, v, l)$, which returns
  just $v$ if the boolean value of $x$ is $v$ (where $v$ will be true or false),
  otherwise the boolean values of the values in $l$.
  Here, $"bool"(v)$ returns the boolean value as given in @simple-fns.
  $ "junction"(x, v, l) := "ite"lr(("bool"(x), v, stream(v), sum_(y in l) stream("bool"(y))), size: #50%) $
- $var(x) "or" f$: Similar to its "and" counterpart above.
- $"if" var(x) "then" f "else" g$: Returns the output of $f$ if $var(x)$ is bound to either null or false, else returns the output of $g$.
- $.[]$, $.[var(x)]$, or $.[var(x):var(y)]$: Accesses parts of the input value; see @accessing for the definitions of the operators.
- $fold x "as" var(x) (.; f)$: Folds $f$ over the values returned by $x$,
  starting with the current input as accumulator.
  The current accumulator value is provided to $f$ as input value and
  $f$ can access the current value of $x$ by $var(x)$.
  If $fold = "reduce" $, this returns only the final        values of the accumulator, whereas
  if $fold = "foreach"$, this returns also the intermediate values of the accumulator.
  We will define the functions
  $"reduce" ^c_v (l, var(x), f)$ and
  $"foreach"^c_v (l, var(x), f)$ in @folding.
- $x(f_1; ...; f_n)$: Calls an $n$-ary filter $x$ that is defined by $x(x_1; ...; x_n) := f$.
  The output is that of the filter $f$, where
  each filter argument $x_i$ is bound to $(f_i, c)$.
  This also handles the case of calling nullary filters such as $"empty"$.
- $x$: Calls a filter argument.
  By the well-formedness requirements given in @hir,
  this must occur within the right-hand side of a definition whose arguments include $x$.
  This requirement also ensures that $x in "dom"(c)$,
  because an $x$ can only be evaluated as part of a call to the filter where it was bound, and
  by the semantics of filter calls above, this adds a binding for $x$ to the context.
- $f update g$: Updates the input at positions returned by $f$ by $g$.
  We will discuss this in @updates.

An implementation may also define custom semantics for named filters.
For example, an implementation may define
$"error"|^c_v := "error"(v)$,
$"keys"|^c_v := "keys"(v)$, and
$"length"|^c_v := |v|$, see @simple-fns.
In the case of $"keys"$, for example, there is no obvious way to implement it by definition,
in particular because there is no simple way to obtain the domain of an object ${...}$
using only the filters for which we gave semantics in @tab:eval-semantics.
For $"length"$, we could give a definition, using
$"reduce" .[] "as" var(x) (0; . + 1)$ to obtain the length of arrays and objects, but
this would inherently require linear time to yield a result, instead of
constant time that can be achieved by a proper jq implementation.


== Folding <folding>

In this subsection, we will define the functions $fold^c_v (l, var(x), f)$
(where $fold$ is either $"foreach"$ or $"reduce"$),
which underlie the semantics for the folding operators
$fold x "as" var(x) (.; f)$.

Let us start by defining a general folding function $"fold"^c_v (l, var(x), f, o)$: It takes
a stream of value results $l$,
a variable $var(x)$,
a filter $f$, and
a function $o(x)$ from a value $x$ to a stream of values.
This function folds over the elements in $l$, starting from the accumulator value $v$.
It yields the next accumulator value(s) by evaluating $f$
with the current accumulator value as input and
with the variable $var(x)$ bound to the first element in $l$.
If $l$ is empty, then
$v$ is called a  _final_        accumulator value and is returned, otherwise
$v$ is called an _intermediate_ accumulator value and $o(v)$ is returned.

$ "fold"^c_v (l, var(x), f, o) := cases(
  o(v) + sum_(x in f|^(c{var(x) |-> h})_v) "fold"^c_x (t, var(x), f, o) & "if" l = stream(h) + t,
  stream(        v ) & "otherwise" (l = stream())
) $

We use two different functions for $o(v)$;
the first returns nothing,  corresponding to $"reduce" $ which does not return intermediate values, and
the other returns just $v$, corresponding to $"foreach"$ which returns intermediate values.
Instantiating $"fold"$ with these two functions, we obtain the following:

$ "reduce"^c_v (l, var(x), f) :=& "fold"^c_v (l, var(x), f, o) "where" o(v) = stream(#hide[v]) \
     "for"^c_v (l, var(x), f) :=& "fold"^c_v (l, var(x), f, o) "where" o(v) = stream(v)
$

Here, $"reduce"^c_v (l, var(x), f)$ is the function that is used in @tab:eval-semantics.
However, $"for"^c_v (l, var(x), f)$ does _not_ implement the semantics of $"foreach"$,
because it yields the initial accumulator value, whereas $"foreach"$ omits it.

#example[
  If we would set $"foreach"^c_v (l, var(x), f) := "for"^c_v (l, var(x), f)$, then evaluating
  $"foreach" (1, 2, 3) "as" var(x) (0; . + var(x))$ would yield
  $stream(0, 1, 3, 6)$, but jq evaluates it to
  $stream(   1, 3, 6)$.
]

For that reason, we define $"foreach"$ in terms of $"for"$,
but with a special treatment for the initial accumulator:

$ "foreach"^c_v (l, var(x), f) := cases(
  sum_(x in f|^(c{var(x) |-> h})_v) "for"^c_x (t, var(x), f) & "if" l = stream(h) + t,
  stream() & "otherwise",
) $

We will now look at what the evaluation of the various folding filters expands to.
Apart from $"reduce"$ and $"foreach"$, we will also consider a hypothetical filter
$"for" x "as" var(x) (.; f)$ that is defined by the function
$"for"^c_v (l, var(x), f)$, analogously to the other folding filters.

Assuming that the filter $x$ evaluates to $stream(x_0, ..., x_n)$,
then $"reduce"$ and $"for"$ expand to

$ "reduce"   x "as" var(x) (.; f) =&     x_0 "as" var(x) | f & wide
  "for"      x "as" var(x) (.; f) =& ., (x_0 "as" var(x) | f \
|& ... &
|& ... \
|&     x_n "as" var(x) | f &
|& ., (x_n "as" var(x) | f)...)
$
and $"foreach"$ expands to
$ "foreach" x "as" var(x) (.; f)
=&     x_0 "as" var(x) | f \
|& ., (x_1 "as" var(x) | f \
|& ... \
|& ., (x_n "as" var(x) | f)...).
$

We can see that the special treatment of the initial accumulator value also shows up
in the expansion of $"foreach"$.
In contrast, the hypothetical $"for"$ filter looks more symmetrical to $"reduce"$.

Note that jq implements only a restricted version of these folding operators
that discards all output values of $f$ after the first output.
That means that in jq,
$fold x "as" var(x) (.;         f )$ is equivalent to
$fold x "as" var(x) (.; "first"(f))$.
Here, we assume the definition $"first"(f) := "label" var(x) | f | (., "break" var(x))$.
This returns the first output of $f$ if $f$ yields any output, else nothing.



= Update Semantics <updates>

In this section, we will discuss how to evaluate updates $f update g$.
First, we will show how the original jq implementation executes such updates,
and show which problems this approach entails.
Then, we will give alternative semantics for updates that avoids these problems,
while enabling faster performance by forgoing the construction of temporary path data.

== jq updates via paths <jq-updates>

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
] <ex:arr-update>

This approach can yield surprising results when the execution of the filter $g$
changes the input value in a way that the set of paths changes midway.
In such cases, only the paths constructed from the initial input are considered.
This can lead to
paths pointing to the wrong data,
paths pointing to non-existent data, and
missing paths.

#example[
  Consider the input value ${qs(a) |-> {qs(b) |-> 1}}$ and the filter
  $(.[], .[][]) update g$, where $g$ is $[]$.
  Executing this filter in jq first builds the path
  $.[qs(a)]$ stemming from "$.[]$", then
  $.[qs(a)][qs(b)]$ stemming from "$.[][]$".
  Next, jq folds over the paths,
  using the input value as initial accumulator and
  updating the accumulator at each path with $g$.
  The final output is thus the output of $(.[qs(a)] update g) | (.[qs(a)][qs(b)] update g)$.
  The output of the first step $.[qs(a)] update g$ is ${qs(a) |-> []}$.
  This value is the input to the second step $.[qs(a)][qs(b)] update g$,
  which yields an error because
  we cannot index the array $[]$ at the path $.[qs(a)]$ by $.[qs(b)]$.
] <ex:obj-update-arr>

/*
// TODO: this actually returns [1, 3] in jq 1.7
One of these problems is that if $g$ returns no output,
the collected paths may point to values that do not exist any more.

#example[
  Consider the input value $[1, 2, 2, 3]$ and the filter
  // '.[] |= (if . == 2 then empty else . end)'
  "$.[] update g$", where $g$ is "$"if" . eq.quest 2 "then" "empty"() "else" .$",
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
*/

We can also have surprising behaviour that does not manifest any error.

#example[
  Consider the same input value and filter as in @ex:obj-update-arr,
  but now with $g$ set to ${qs(c): 2}$.
  The output of the first step $.[qs(a)] update g$ is ${qs(a) |-> {qs(c) |-> 2}}$.
  This value is the input to the second step $.[qs(a)][qs(b)] update g$, which yields
  ${qs(a) |-> {qs(c) |-> 2, qs(b) |-> {qs(c) |-> 2}}}$.
  Here, the remaining path ($.[qs(a)][qs(b)]$) pointed to
  data that was removed by the update on the first path,
  so this data gets reintroduced by the update.
  On the other hand, the data introduced by the first update step
  (at the path $.[qs(a)][qs(c)]$) is not part of the original path,
  so it is _not_ updated.
] <ex:obj-update-obj>

We found that we can interpret many update filters by simpler filters,
yielding the same output as jq in most common cases, but avoiding the problems shown above.
To see this, let us see what would happen if we would interpret
$(f_1, f_2) update g$ as $(f_1 update g) | (f_2 update g)$.
That way, the paths of $f_2$ would point precisely to the data returned by
$f_1 update g$, thus avoiding the problems depicted by the examples above.
In particular, with such an approach,
@ex:obj-update-arr would yield ${qs(a) |-> []}$ instead of an error, and
@ex:obj-update-obj would yield ${qs(a) |-> {qs(c) |-> {qs(c) |-> 2}}}$.

In the remainder of this section, we will show
semantics that extend this idea to all update operations.
The resulting update semantics can be understood to _interleave_ calls to $f$ and $g$.
By doing so, these semantics can abandon the construction of paths altogether,
which results in higher performance when evaluating updates.

== Properties of new semantics

// μονοπάτι = path
// συνάρτηση = function
#figure(caption: [Update semantics properties.], table(columns: 2,
  $mu$, $mu update sigma$,
  $"empty"()$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $"if" var(x) "then" f "else" g$, $"if" var(x) "then" f update sigma "else" g update sigma$,
  $f alt g$, $"if" "first"(f alt "null") "then" f update sigma "else" g update sigma$,
)) <tab:update-props>

@tab:update-props gives a few properties that we want to hold for updates $mu update sigma$.
Let us discuss these for the different filters $mu$:
- $"empty"()$: Returns the input unchanged.
- "$.$": Returns the output of the update filter $sigma$ applied to the current input.
  Note that while jq only returns at most one output of $sigma$,
  these semantics return an arbitrary number of outputs.
- $f | g$: Updates at $f$ with the update of $sigma$ at $g$.
  This allows us to interpret
  $(.[] | .[]) update sigma$ in @ex:arr-update by
  $.[] update (.[] update sigma)$, yielding the same output as in the example.
- $f, g$: Applies the update of $sigma$ at $g$ to the output of the update of $sigma$ at $f$.
  We have already seen this at the end of @jq-updates.
- $"if" var(x) "then" f "else" g$: Applies $sigma$ at $f$ if $var(x)$ holds, else at $g$.
- $f alt g$: Applies $sigma$ at $f$ if $f$ yields some output whose boolean value (see @simple-fns) is not false, else applies $sigma$ at $g$.
  See @folding for the definition of $"first"$.

While @tab:update-props allows us to define the behaviour of several filters
by reducing them to more primitive filters,
there are several filters $mu$ which cannot be defined this way.
We will therefore give the actual update semantics of $mu update sigma$ in @new-semantics
by defining $(mu update sigma)|^c_v$, not
by translating $mu update sigma$ to equivalent filters.

== Limiting interactions <limiting-interactions>

To define $(mu update sigma)|^c_v$, we first have to understand
how to prevent unwanted interactions between $mu$ and $sigma$.
In particular, we have to look at variable bindings and error catching.

=== Variable bindings <var-bindings>

We can bind variables in $mu$; that is, $mu$ can have the shape $f "as" var(x) | g$.
Here, the intent is that $g$ has access to $var(x)$, whereas $sigma$ does not!
This is to ensure compatibility with jq's original semantics,
which execute $mu$ and $sigma$ independently,
so $sigma$ should not be able to access variables bound in $mu$.

#example[
  Consider the filter $0 "as" var(x) | mu update sigma$, where
  $mu$ is $(1 "as" var(x) | .[var(x)])$ and $sigma$ is $var(x)$.
  This updates the input array at index $1$.
  If $sigma$ had access to variables bound in $mu$,
  then the array element would be replaced by $1$,
  because the variable binding $0 "as" var(x)$ would be shadowed by $1 "as" var(x)$.
  However, in jq, $sigma$ does not have access to variables bound in $mu$, so
  the array element is replaced by $0$, which is the value originally bound to $var(x)$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.
]

We take the following approach to prevent variables bound in $mu$ to "leak" into $sigma$:
When evaluating $(mu update sigma)|^c_v$, we want
$sigma$ to always be executed with the same $c$.
That is, evaluating $(mu update sigma)|^c_v$ should never
evaluate $sigma$ with any context other than $c$.
In order to ensure that, we will define
$(mu update sigma)|^c_v$ not for a _filter_ $sigma$,
but for a _function_ $sigma(x)$, where
$sigma(x)$ returns the output of the filter $sigma|^c_x$.
This allows us to extend the context $c$ with bindings on the left-hand side of the update,
while executing the update filter $sigma$ always with the same original context $c$.

=== Error catching <error-catching>

We can catch errors in $mu$; that is, $mu$ can have the shape $"try" f "catch" g$.
However, this should catch only errors that occur in $mu$,
_not_ errors that are returned by $sigma$.

#example[
  Consider the filter $mu update sigma$, where $mu$ is $.[]?$ and $sigma$ is $.+1$.
  The filter $mu$ is lowered to the MIR filter $"try" .[] "catch" "empty"()$.
  The intention of $mu update sigma$ is to
  update all elements $.[]$ of the input value, and if $.[]$ returns an error
  (which occurs when the input is neither an array nor an object, see @accessing),
  to just return the input value unchanged.
  When we run $mu update sigma$ with the input $0$,
  the filter $.[]$ fails with an error, but
  because the error is caught immediately afterwards,
  $mu update sigma$ consequently just returns the original input value $0$.
  The interesting part is what happens when $sigma$ throws an error:
  This occurs for example when running the filter with the input $[{}]$.
  This would run $. + 1$ with the input ${}$, which yields an error (see @arithmetic).
  This error _is_ returned by $mu update sigma$.
]

This raises the question:
How can we execute $("try" f "catch" g) update sigma$ and distinguish
errors stemming from $f$ from errors stemming from $sigma$?

We came up with the solution of _polarised exceptions_.
In a nutshell, we want every exception that is returned by $sigma$ to be
marked in a special way such that it can be ignored by a try-catch in $mu$.
For this, we assume the existence of two functions
$"polarise"(x)$ and $"depolarise"(x)$ from a value result $x$ to a value result.
If $x$ is an exception, then
$"polarise"(x)$ should return a polarised version of it, whereas
$"depolarise"(x)$ should return an unpolarised version of it, i.e. it should
remove any polarisation from an exception.
Every exception created by $"error"(e)$ is unpolarised.
With this method, when we evaluate an expression $"try" f "catch" g$ in $mu$,
we can analyse the output of $f update sigma$, and only catch _unpolarised_ errors.
That way, errors stemming from $mu$ are propagated,
whereas errors stemming from $f$ are caught.


== New semantics <new-semantics>

We will now give semantics that define the output of
$(f update g)|^c_v$ as referred to in @semantics.

We will first combine the techniques in @limiting-interactions to define
$(f update g)|^c_v$ for two _filters_ $f$ and $g$ by
$(f update sigma)|^c_v$, where
$sigma$ now is a _function_ from a value to a stream of value results:
$ (f update g)|^c_v := sum_(y in (f update sigma)|^c_v) "depolarise"(y)", where"
sigma(x) = sum_(y in g|^c_x) "polarise"(y). $
We use a function instead of a filter on the right-hand side to
limit the scope of variable bindings as explained in @var-bindings, and
we use $"polarise"$ to
restrict the scope of caught exceptions, as discussed in @error-catching.
Note that we $"depolarise"$ the final outputs of $f update g$ in order to
prevent leaking polarisation information outside the update.

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
  $"break" var(x)$, $stream("break"(var(x)))$,
  $x(f_1; ...; f_n)$, $(f update sigma)|^(c union union.big_i {x_i |-> (f_i, c)})_v "if" x(x_1; ...; x_n) := f$,
  $x$, $(f update sigma)|^c'_v "if" c(x) = (f, c')$,
)) <tab:update-semantics>

@tab:update-semantics shows the definition of $(mu update sigma)|^c_v$.
Several of the cases for $mu$, like
"$.$", "$f | g$", "$f, g$", and "$"if" var(x) "then" f "else" g$"
are simply relatively straightforward consequences of the properties in @tab:update-props.
We discuss the remaining cases for $mu$:
- $f alt g$: Updates using $f$ if $f$ yields some non-false value, else updates using $g$.
  Here, $f$ is called as a "probe" first.
  If it yields at least one output that is considered "true"
  (see @semantics for the definition of $"trues"$),
  then we update at $f$, else at $g$.
  This filter is unusual because is the only kind where a subexpression is both
  updated with ($(f update sigma)|^c_v$) and evaluated ($f|^c_v$).
- $.[]$, $.[var(x)]$, $.[var(x) : var(y)]$:
  Applies $sigma$ to the current value using the operators defined in @updating.
- $f "as" var(x) | g$:
  Folds over all outputs of $f$, using the input value $v$ as initial accumulator and
  updating the accumulator by $g update sigma$, where
  $var(x)$ is bound to the current output of $f$.
  The definition of $"reduce"$ is given in @folding.
- $"try" f "catch" g$: Returns the output of $f update sigma$,
  mapping errors occurring in $f$ to $g$. The definition of the function $"catch"$ is
  $ "catch"(x, g, c, v) := cases(
    sum_(y in g|^c_(e)) stream("error"(y)) & "if" x = "error"(e)", " x "is unpolarised, and" g|^c_x != stream(),
    stream(v) & "if" x = "error"(e)", " x "is unpolarised, and" g|^c_x = stream(),
    stream(x) & "otherwise"
) $
  The function $"catch"(x, g, c, v)$ analyses $x$ (the current output of $f$):
  If $x$ is no unpolarised error, $x$ is returned.
  For example, that is the case if the original right-hand side of the update
  returns an error, in which case we do not want this error to be caught here.
  However, if $x$ is an unpolarised error, that is,
  an error that was caused on the left-hand side of the update,
  it has to be caught here.
  In that case, $"catch"$ analyses the output of $g$ with input $x$:
  If $g$ yields no output, then it returns the original input value $v$,
  and if $g$ yields output, all its output is mapped to errors!
  This behaviour might seem peculiar,
  but it makes sense when we consider the jq way of implementing updates via paths:
  When evaluating some update $mu update sigma$ with an input value $v$,
  the filter $mu$ may only return paths to data contained within $v$.
  When $mu$ is $"try" f "catch" g$,
  the filter $g$ only receives inputs that stem from errors,
  and because $v$ cannot contain errors, these inputs cannot be contained in $v$.
  Consequentially, $g$ can never return any path pointing to $v$.
  The only way, therefore, to get out alive from a $"catch"$ is for $g$ to return ... nothing.
- $"break"(var(x))$: Break out from the update.#footnote[
    Note that unlike in @semantics, we do not define the update semantics of
    $"label" var(x) | f$, which could be used to resume an update after a $"break"$.
    The reason for this is that this requires
    an additional type of $"break"$ exceptions that
    carries the current value alongside the variable, as well as
    variants of the value update operators in @updating that can handle unpolarised breaks.
    Because making update operators handle unpolarised breaks
    renders them considerably more complex and
    we estimate that label expressions are
    rarely used in the left-hand side of updates anyway,
    we think it more beneficial for the presentation to forgo label expressions here.
  ]
- $x(f_1; ...; f_n)$, $x$: Call filters.
  This is defined analogously to @tab:eval-semantics.

There are many filters $mu$ for which
$(mu update sigma)|^c_v$ is not defined,
for example $var(x)$, $[f]$, and ${}$.
In such cases, we assume that $(mu update sigma)|^c_v$ returns an error just like jq,
because these filters do not return paths to their input data.#footnote[
  Apart from $"label" var(x) | g$, there is only one other kind of filter $mu$
  that is supported in jq but not in our semantics, namely $fold x "as" var(x)(.; f)$.
  For the final version of this text, however, we hope to provide
  update semantics for this kind of filters as well.
]

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



= Equational reasoning showcase: Object Construction <obj-eq>

We will now show how to prove properties about HIR filters by equational reasoning.
For this, we use the lowering in @mir and the semantics defined in @semantics.
As an example, we will show a few properties of object construction.

Let us start by proving a few helper lemmas, where
$c$ and $v$ always denote some arbitrary context and value, respectively.

#lemma[
  For any HIR filters $f$ and $g$ and any Cartesian operator $cartesian$
  (such as addition, see @tab:binops),
  we have $floor(f cartesian g)|^c_v = sum_(x in floor(f)|^c_v) sum_(y in floor(g)|^c_v) stream(x cartesian y)$.
] <lem:cart-sum>

#proof[
  The lowering in @tab:lowering yields
  $floor(f cartesian g)|^c_v = (floor(f) "as" var(x') | floor(g) "as" var(y') | var(x') cartesian var(y'))|^c_v$.
  Using the evaluation semantics in @tab:eval-semantics, we can further expand this to
  $sum_(x in floor(f)|^c_v) sum_(y in floor(g)^c{var(x') |-> x}_v)
  (var(x') cartesian var(y'))|^c{var(x') |-> x, var(y') |-> y}_v$.
  Because $var(x')$ and $var(y')$ are fresh variables,
  we know that they cannot occur in $floor(g)$, so
  $floor(g)^c{var(x') |-> x}_v = floor(g)^c_v$.
  Furthermore, by the evaluation semantics, we have
  $(var(x') cartesian var(y'))|^c{var(x') |-> x, var(y') |-> y}_v = stream(x cartesian y)$.
  From these two observations, the conclusion immediately follows.
]

#lemma[
  For any HIR filters $f$ and $g$, we have
  $floor({f: g})|^c_v = sum_(x in floor(f)|^c_v) sum_(y in floor(g)|^c_v) stream({x: y})$.
] <lem:obj-sum>

#proof[Analogously to the proof of @lem:cart-sum.]

We can now proceed by stating a central property of object construction.

#theorem[
  For any $n in NN$ with $n > 0$, we have that
  $floor({k_1: v_1, ..., k_n: v_n})|^c_v$ is equivalent to
  $ sum_(k_1 in floor(k_1)|^c_v)
    sum_(v_1 in floor(v_1)|^c_v) ...
    sum_(k_n in floor(k_n)|^c_v)
    sum_(v_n in floor(v_n)|^c_v)
    stream(sum_i {k_i: v_i}).
  $
]

#proof[
  We will prove by induction on $n$.
  The base case $n = 1$ directly follows from @lem:obj-sum.
  For the induction step, we have to show that
  $floor({k_1: v_1, ..., k_(n+1): v_(n+1)})|^c_v$ is equivalent to
  $ sum_(k_1 in floor(k_1)|^c_v)
    sum_(v_1 in floor(v_1)|^c_v) ...
    sum_(k_(n+1) in floor(k_(n+1))|^c_v)
    sum_(v_(n+1) in floor(v_(n+1))|^c_v)
    stream(sum_i^(n+1) {k_i: v_i}).
  $
  We start by
  $ & floor({k_1: v_1, ..., k_(n+1): v_(n+1)})|^c_v =^"(lowering)" \
  = & floor(sum_i {k_i: v_i})|^c_v = \
  = & floor(sum_(i = 1)^n {k_i: v_i} + {k_(n+1): v_(n+1)})|^c_v =^#[(@lem:cart-sum)] \
  = & sum_(x in floor(sum_(i=1)^n {k_i: v_i})|^c_v)
      sum_(y in floor({k_(n+1): v_(n+1)})|^c_v)
      stream(x + y).
  $
  Here, we observe that
  $floor(sum_(i=1)^n {k_i: v_i})|^c_v = floor({k_1: v_1, ..., k_n: v_n})|^c_v$,
  which by the induction hypothesis equals
  $ sum_(k_1 in floor(k_1)|^c_v)
    sum_(v_1 in floor(v_1)|^c_v) ...
    sum_(k_n in floor(k_n)|^c_v)
    sum_(v_n in floor(v_n)|^c_v)
    stream(sum_i^n {k_i: v_i}).
  $
  We can use this to resume the simplification of
  $floor({k_1: v_1, ..., k_(n+1): v_(n+1)})|^c_v$ to
  $ sum_(k_1 in floor(k_1)|^c_v)
    sum_(v_1 in floor(v_1)|^c_v) ...
    sum_(k_n in floor(k_n)|^c_v)
    sum_(v_n in floor(v_n)|^c_v)
    sum_(y in floor({k_(n+1): v_(n+1)})|^c_v)
    stream(sum_i^n {k_i: v_i} + y)
  $
  Finally, applying @lem:obj-sum to $floor({k_(n+1): v_(n+1)})|^c_v$ proves the induction step.
]

We can use this theorem to simplify the evaluation of filters such as the following one.

#example[
  The evaluation of
  ${qs(a): (1, 2), (qs(b), qs(c)): 3, qs(d): 4}$
  //(with arbitrary context and input)
  yields $stream(v_0, v_1, v_2, v_3)$, where $
  v_0 = {qs(a) |-> 1, qs(b) |-> 3, qs(d) |-> 4},\
  v_1 = {qs(a) |-> 1, qs(c) |-> 3, qs(d) |-> 4},\
  v_2 = {qs(a) |-> 2, qs(b) |-> 3, qs(d) |-> 4},\
  v_3 = {qs(a) |-> 2, qs(c) |-> 3, qs(d) |-> 4}.
  $
]



= Conclusion

We have shown formal syntax and semantics of
a large subset of the jq programming language.

On the syntax side, we first defined
formal syntax (HIR) that closely corresponds to actual jq syntax.
We then gave a lowering that reduces HIR to a simpler subset (MIR),
in order to simplify the semantics later.
We finally showed how a subset of actual jq syntax can be translated into HIR and thus MIR.

On the semantics side, we gave formal semantics based on MIR.
First, we defined values and basic operations on them.
Then, we used this to define the semantics of jq programs,
by specifying the outcome of the execution of a jq program.
A large part of this was dedicated to the evaluation of updates:
In particular, we showed a new approach to evaluate updates.
This approach, unlike the approach implemented in jq,
does not depend on separating path building and updating, but interweaves them.
This allows update operations to cleanly handle multiple output values
in cases where this was not possible before.
Furthermore, in practice, this avoids creating temporary data to store paths,
thus improving performance.
This approach is also mostly compatible with the original jq behaviour,
yet it is unavoidable that it diverges in some corner cases.

We hope that our work is useful in several ways:
For users of the jq programming language, it provides
a succinct reference that precisely documents the language.
Our work should also benefit implementers of tools that process jq programs,
such as compilers, interpreters, or linters.
In particular, this specification should be sufficient to
implement the core of a jq compiler or interpreter.
Finally, our work enables equational reasoning about jq programs.
This makes it possible to prove correctness of jq programs or to
implement provably correct optimisations in jq compilers/interpreters.

#bibliography("literature.bib")
