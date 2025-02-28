#import "@preview/diagraph:0.3.1"
#import "@preview/ctheorems:1.1.3"
#import "acm.typ": acmart
#import "common.typ": *
#show: ctheorems.thmrules

#show: acmart.with(
  format: "acmsmall",
  // TODO: set to true!
  draft: false,
  anonymous: true,

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
However, the jq language is currently only specified by its implementation,
making it difficult to reason about its behaviour.
To this end, we provide a formal syntax and denotational semantics for
a large subset of the jq language.
In particular, we give a translation from jq programs to lambda terms.
Our most significant contribution is to provide a new way to interpret updates
that allows for more predictable and performant execution.
We implement our semantics in a interpreter and evaluate its performance,
showing that it executes jq programs faster than any other jq implementation.
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

jq is a tool that
provides a language to define filters and
executes programs written in that language.
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
/*
However, the documentation frequently does not cover certain cases, and
historically, the implementation often contradicted the documentation.
For example, the documentation stated that the filter `limit(n; f)`
"extracts up to `n` outputs from `f`".
However, `limit(0; f)` extracts up to 1 outputs from `f`, and
for negative values of `n`, `limit(n; f)` extracts all outputs of `f`.
*/
This leaves a lot of space for interpretation and makes it difficult to find out
whether certain behaviour of a jq implementation is accidental or intended.

We have striven to create denotational semantics (@semantics) that
closely resemble those of jq such that in most common use cases,
their behaviour coincides, whereas they may differ in more exotic cases.
The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe, understand, and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.

We created these semantics experimentally, by coming up with
jq filters and observing their output for all kinds of inputs.

One of the least specified, yet most fascinating features of the jq language
are _updates_:
An update filter, such as `f |= g`, modifies input data using
a filter `f` that defines which parts of the input to update, and
a filter `g` that defines what the matching input parts should be replaced with.
We found a new approach to updates which
can be described compactly and unambiguously,
eliminates many potential errors, and
allows for more performant execution.
The original semantics of jq and those that will be shown in this text
differ most notably in the case of updates;
yet in most common use cases, both semantics yield equal results.

The structure of this text is as follows:
@tour introduces jq by a series of examples that
give a glimpse of actual jq syntax and behaviour.
From that point on, the structure of the text follows
the execution of a jq program as shown in @fig:structure.
@syntax formalises a subset of jq syntax and shows how jq syntax can be
transformed to increasingly low-level intermediate representations called
HIR (@hir) and MIR (@mir).
After this, the semantics part starts:
@values defines several data types and corresponding lambda terms, such as
values, value results, and lists.
@semantics shows how to evaluate jq filters on a given input value.
@updates presents our new approach to executing updates and
compares it with the traditional approach used in jq.
@impl describes and evaluates a jq interpreter based on our proposed semantics.
It turns out that on 25 out of 29 benchmark programs,
our interpreter is the fastest of all evaluated jq implementations.

#figure(caption: [Our approach to evaluate a jq program with an input value.
  Solid lines indicate data flow, whereas a dashed line indicates that
  a component is defined in terms of another.
], diagraph.render(read("structure.dot"))) <fig:structure>


#include "tour.typ"
#include "syntax.typ"
#include "values.typ"
#include "semantics.typ"
#include "impl.typ"


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
by specifying how to compile a jq program to a lambda term.
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

Finally, we presented our implementation `jaq` of the new semantics and
showed that its performance is best-in-class for jq implementations.
Furthermore, we showed that indeed, the new update semantics yield
particularly large speed-ups, compared to other operations.

We hope that our work is useful in several ways:
For users of the jq programming language, it provides
a succinct reference that precisely documents the language.
Our work should also benefit implementers of tools that process jq programs,
such as compilers, interpreters, or linters.
In particular, this specification should be sufficient to
implement the core of a jq compiler or interpreter.

#bibliography("literature.bib")

#let appendix(body) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  counter(heading).update(0)
  body
}

#show: appendix

#include "json.typ"
