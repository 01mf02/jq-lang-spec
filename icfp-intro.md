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

jq is a tool that
provides a language to define filters and
executes programs written in that language.
Where UNIX filters operate on streams of characters,
jq filters operate on streams of JSON values.
This allows to manipulate JSON data with relatively compact filters.
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
This makes jq a widely used tool.
We refer to the program jq as "jq" and to its language as "the jq language".

The jq language is a dynamically typed, lazily evaluated
functional programming language with
second-class higher-order functions [@jq-description].
The semantics of the jq language are only
informally specified, for example in the jq manual [@jq-manual].
This leaves a lot of space for interpretation and makes it difficult to find out
whether certain behaviour of a jq implementation is accidental or intended.

We have striven to create denotational semantics (@sec:semantics) that
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
@sec:tour introduces jq by a series of examples that
give a glimpse of actual jq syntax and behaviour.
From that point on, the structure of the text follows
the execution of a jq program as shown in @fig:structure.
@sec:syntax formalises a subset of jq syntax and shows how jq syntax can be
transformed to a more low-level intermediate representation called IR (@sec:mir).
After this, the semantics part starts:
@sec:values defines several data types and corresponding lambda terms, such as
values, value results, and lists.
@sec:semantics shows how to evaluate jq filters on a given input value.
@sec:updates presents our new approach to executing updates and
compares it with the traditional approach used in jq.
@sec:impl describes and evaluates a jq interpreter based on our proposed semantics.
It turns out that on 25 out of 29 benchmark programs,
our interpreter is the fastest of all evaluated jq implementations.

\begin{figure}
\centering
\resizebox{\textwidth}{!}{
\input{structure}
}
\caption{
  Our approach to evaluate a jq program with an input value.
  Solid lines indicate data flow, whereas a dashed line indicates that
  a component is defined in terms of another.
}
\label{fig:structure}
\end{figure}
