#import "@preview/diagraph:0.3.1"
#import "@preview/ctheorems:1.1.3"
#import "acm.typ": acmart
#import "common.typ": *
#show: ctheorems.thmrules

#show: acmart.with(
  format: "acmsmall",
  // TODO: set to true!
  draft: false,

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
  anonymous: false,
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

  pub: none, /*(
    journal: "Journal of the ACM",
    journal-short: "J. ACM",
    volume: 37,
    number: 4,
    article: 1,
    month: 8,
    year: 2018,
    doi: "XXXXXXX.XXXXXXX",
  ),
  */
  copyright: pub => [
    #line(length: 30%, stroke: 0.5pt)
    #link("https://creativecommons.org/licenses/by/4.0/")[
      #image("cc-by.svg", width: 10%)
      This work is licensed under a Creative Commons Attribution 4.0 International License.
    ] \
    © 2024 Copyright held by the owner/author(s).
  ],
)

#set raw(lang: "jq")
#set figure(placement: auto)
#set table(fill: (_, y) => if y == 0 { gray.lighten(75%) })

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

We have striven to create denotational semantics (@semantics) that
closely resemble those of jq such that in most common use cases,
their behaviour coincides, whereas they may differ in more exotic cases.
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
//Finally, we show how to prove properties of jq programs by equational reasoning in @obj-eq.

#figure(caption: [Evaluation of a jq program with an input value.
  Solid lines indicate data flow, whereas a dashed line indicates that
  a component is defined in terms of another.
], diagraph.render(read("structure.dot"))) <fig:structure>



#include "tour.typ"
#include "syntax.typ"
#include "values.typ"
#include "semantics.typ"

/*

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

*/

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

#let appendix(body) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  counter(heading).update(0)
  body
}

#show: appendix

#include "json.typ"
