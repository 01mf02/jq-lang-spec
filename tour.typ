#import "common.typ": example

= Tour of jq <tour>

This goal of this section is to convey an intuition about how jq functions.
The official documentation of jq is its user manual @jq-manual.

jq programs are called _filters_.
For now, let us consider a filter to be a function from a value to
a (lazy, possibly infinite) stream of values.
Furthermore, in this section, let us assume a value to be either
a boolean, an integer, or an array of values.
(We introduce the full set of JSON values in @json.)

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

Wherever we can use `as $x` to bind values to a variable,
we can also destructure values using a _pattern_.
For example, given the input value `[1, [2], 3]`, the filter
`. as [$x, [$y], $z] | $y` yields `2`.

We can halt filter evaluation with `label`-`break`:
The filter `label $x | f` yields all outputs of `f`
until `f` invokes `break $x`, at which point `f` is not evaluated further.
For example, the filter
`(label $x | 1, break $x, 2), 3` yields the stream `1, 3`.
It is possible to break out from arguments passed to filters;
for example, the filter `label $x | recurse(break $x)` returns its input.
We can also nest labels; for example, the filter
`label $x | 1, (label $y | 2, break $x, 3), 4` yields `1, 2`.
If we replace `break $x` by `break $y`, then it yields `1, 2, 4`.
If we replace `break $x` by `empty`, then it yields `1, 2, 3, 4`.

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
