#import "@preview/ctheorems:1.1.0"
#import "common.typ": *

#show: ctheorems.thmrules
#set heading(numbering: "1.1")

#let title = [A formal specification of the jq language]

#text(size: 20pt, weight: "bold", title)

= Introduction

`jq` is a tool that provides a programming language
to efficiently process JSON data.
We call this programming language the "jq language".
It is documented by the user manual @jq-manual.
However, the user manual can be ambiguous or even
contradict the behaviour of `jq`.

This text aims to give a precise, mathematical description of the jq language, similar to
the "WebAssembly Core Specification" for WebAssembly @WebAssemblyCoreSpecification2.
It is intended to complement the user manual.
In some places, the behaviour described in this text diverges from `jq`.
We try to point out such differing behaviour whenever it occurs.

/*
Note that this text only aims to specify
the behaviour of jq filters that have special syntax, such as `|`;
it does not attempt to specify
the behaviour of particular named filters, such as `reverse`.
*/

This text is structured as follows:
@tour gives an introduction to the jq language.
@syntax specifies the syntax treated in this text and transforms it to a simpler subset.
@values defines JSON values as well as some operations on them used in jq.
@semantics defines the output of jq programs, and
@updates defines the output of jq updates.

#include "tour.typ"
#include "syntax.typ"
#include "values.typ"
#include "semantics.typ"

#bibliography("literature.bib")
