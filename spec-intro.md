# Introduction

`jq` is a tool that provides a programming language
to efficiently process JSON data.
We call this programming language the "jq language".

This text aims to give a precise, mathematical description of the jq language, similar to
the "WebAssembly Core Specification" for WebAssembly [@WebAssemblyCoreSpecification2].
It is intended to complement the user manual [@jq-manual].
In some places, the behaviour described in this text diverges from `jq`.
We try to point out such differing behaviour whenever it occurs.

The first and foremost goal of this text is to allow users to
_precisely predict what their jq programs will output_.
On the other hand, this text does not try to describe how
to implement a performant interpreter for the jq language --- the focus is not
on _how_ a jq interpreter executes a jq program, but
on _what_ a jq program outputs.
This differentiates this text from the jq language description [@jq-description],
which draws much stronger on the implementation of `jq` to describe the jq language.

This text does not cover all parts of the jq language;
in particular, it does not cover the module system.
However, most of the programs that use features not covered by this specification
can be translated into programs that are completely covered by this specification.
For example, a program made of several modules can be
transformed into a program that does not use modules.

<!--
Note that this text only aims to specify
the behaviour of jq filters that have special syntax, such as `|`;
it does not attempt to specify
the behaviour of particular named filters, such as `reverse`.
-->

This text is structured as follows:
@sec:tour gives an introduction to the jq language.
@sec:syntax specifies the syntax treated in this text and transforms it to a simpler subset.
@sec:values defines values.
@sec:semantics defines the output of jq programs, and
@sec:updates defines the output of jq updates.
Finally,
@sec:json defines JSON values as well as some operations on them used in jq.
