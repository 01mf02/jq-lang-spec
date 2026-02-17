UNIX has popularised the concept of _filters_ and _pipes_ [@Ritchie84]:
A filter is a program that reads from an input stream and writes to an output stream.
Pipes are used to compose filters.

JSON (JavaScript Object Notation) is a widely used data serialisation format [@rfc8259].
A JSON value is either
null,
a boolean,
a number,
a string,
an array of values, or
an associative map from strings to values.

`jq` is a widely used tool that
provides a language to define filters and
executes programs written in that language.
Where UNIX filters operate on streams of characters,
jq filters operate on streams of JSON values.
This allows to manipulate JSON data with relatively compact filters.
<!--
For example, given as input the public JSON dataset of streets in Paris [@paris-voies],
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
-->
We refer to the program as "`jq`" and to
its language as "the jq language" or "jq".
A "jq interpreter" is a program that executes jq programs.

The jq language is a dynamically typed, lazily evaluated
functional programming language with
second-class higher-order functions [@jq-description].
The semantics of the jq language are only
informally specified, for example in the jq manual [@jq-manual].
This leaves a lot of space for interpretation and makes it difficult to find out
whether certain behaviour of a jq interpreter is accidental or intended.

We have created denotational semantics (@sec:semantics) for the jq language.
This makes it possible to verify
the correctness of jq programs and interpreters.
For example, our semantics could be used to prove that
an optimisation technique in a jq interpreter is correct.
Furthermore, our semantics are abstract over the type of values.
This accommodates the fact that the type of values differs between
different jq interpreters and different versions of `jq`.
It also makes it possible to describe jq interpreters that
process other kinds of values than JSON.

<!--
The goals for creating these semantics were, in descending order of importance:

- Simplicity: The semantics should be easy to describe, understand, and implement.
- Performance: The semantics should allow for performant execution.
- Compatibility: The semantics should be consistent with jq.
We created these semantics experimentally, by coming up with
jq filters and observing `jq`'s behaviour.
-->

One of the least specified, yet most fascinating features of jq
are _updates_:
An update filter, such as `f |= g`, modifies input data using
a filter `f` that defines which parts of the input to update, and
a filter `g` that defines what the matching input parts should be replaced with.
We found a new approach called _path-less updates_ which
can be described compactly and unambiguously,
eliminates many potential errors, and
allows for more performant execution.
We compare this with jq's traditional path-based updates.

We have implemented two jq interpreters:
_ujq_ is a direct translation of our semantics to Haskell, and
_jaq_ is an optimised version written in Rust.
To test whether a jq interpreter (such as jaq) confirms to our semantics,
we can compare its behaviour to ujq.

@sec:tour introduces jq by a series of examples that
give a glimpse of actual jq syntax and behaviour.
@sec:values defines several data types and corresponding lambda terms, such as
values, results, and lists.
@sec:syntax formalises a subset of jq syntax and shows
how to transform jq syntax to an intermediate representation (IR).
@sec:semantics shows how to evaluate jq filters on a given input value.
@sec:updates presents the traditional path-based and our new path-less approach to executing updates.
@sec:impl describes and evaluates our two jq interpreters.
It shows that our semantics enable performant and correct execution of
several large programs written in jq.
