# Implementation {#sec:impl}

We implemented two interpreters for the jq language, namely ujq and jaq.
ujq is a minimalistic research interpreter that
demonstrates that our semantics can be implemented _compactly_.
jaq is a full-featured interpreter that
demonstrates that our semantics can also be implemented _efficiently_.

## ujq

ujq is a translation of this paper's contents to Haskell,
aiming to provide an minimal executable version of this paper.
In particular, ujq implements
lowering of a jq filter to IR (@sec:ir) and
execution of an IR filter (@sec:semantics).
@sec:ujq explains in more detail how ujq relates to our semantics.

## jaq {#sec:jaq}

jaq is a full-featured jq interpreter written in Rust.
Like ujq, jaq implements the semantics in @sec:semantics, however,
it adds a number of optimisation techniques, such as tail-call optimisation (TCO).
That makes it more difficult to establish by looking at the code that jaq implements our semantics.
However, this can be tested experimentally by comparing outputs of ujq and jaq.
Furthermore, jaq not only implements the core jq language, but also
all syntactic constructs omitted from this specification, such as modules,
as well as more than 90% of jq's standard library.
It demonstrates that the semantics can be implemented efficiently.
To ensure compatibility with `jq`,
jaq has a test suite of more than 500 jq programs
which yield the same output for `jq` and jaq.

The other main jq interpreters, namely `jq` and gojq,
both compile a jq program to a list of imperative instructions and execute it, whereas
jaq compiles a jq program to an abstract syntax tree and interprets it,
yielding an iterator over output values.

jaq's public issue tracker has allowed us to identify which
parts of our semantics cause compatibility problems for jq users.
This is particularly interesting for our path-less update semantics,
where our semantics diverge most notably from `jq`.
<!-- https://github.com/01mf02/jaq/pull/285 -->
Users reported three issues caused by the update semantics described in this paper;
these were all about the semantics of "`.. |= g`".
As explained in @ex:rec-update, our original semantics could cause infinite loops,
and we have since adjusted our semantics to address this issue.
The fact that there were three independent reports of
the same issue related to update semantics shows that users
extensively use updates in jaq and report their issues with it.
The fact that no other issues with update semantics were reported so far
indicates that our new update semantics
preserve compatibility for a vast majority of users.
Most reported issues have been about
the command-line interface and
filters in the standard library.
There are currently no open issues related to
the core jq semantics described in this article.

## Evaluation {#sec:eval}

We evaluated the jq interpreters `jq`, gojq, and jaq^[
  The used versions are
  `jq` 1.8.1,
  gojq 0.12.18, and
  jaq revision 80a0dc0.
]
on a number of programming language interpreters written in the jq language:

- `bf.jq` (35 lines of code) by the author of gojq is an interpreter for the Brainfuck language.
  We run it on `fib.bf`,
  a Brainfuck program that calculates the first 13 Fibonacci numbers.
- `wsjq.jq` (552 LOC) by Thalia Archibald is an interpreter for the Whitespace language [@wsjq].
  We run it on `hopper.ws`,
  a Whitespace program by Dmitry Belov that outputs a portrait of Grace Hopper.
- `jqjq.jq` (2837 LOC) by Mattias Wadman is an interpreter for the jq language [@jqjq].
  We run it on its whole test suite consisting of over 200 tests,
  where each test executes a jq program inside jqjq.

While these are relatively unusual jq programs due to their large size,
they are very useful to test compatibility of jq interpreters,
because they exploit many various language features.
Furthermore, they do not require large input data sets,
so performance results only depend on the jq interpreter,
not on other components such as JSON parsing.

All evaluated jq interpreters, including jaq, yield the same output for all benchmarks.
This shows that our semantics enable a high degree of compatibility with other jq interpreters.

\begin{figure}
\centering
\input{eval/interpreters.tex}
\caption{Time to run a benchmark in various jq interpreters, in milliseconds. Lower is better.}
\label{fig:interpreters}
\end{figure}

The benchmarks were run on a Linux system with an AMD Ryzen 5 5500U.
The results are given in @fig:interpreters.
On "bf-fib", gojq is leading slightly before jaq.
On "wsjq-hopper", jaq achieves the best performance,
being about 60 times (!) as fast as gojq and 5 times as fast as `jq`.
On "jqjq-test", gojq achieves the best performance,
being about twice as fast as jaq.^[
  We only recently found the relatively high runtime of jaq
  on jqjq to be likely caused by a suboptimal handling of tail calls in jaq.
  We are confident to be able to provide better performance results for the final article.
]


<!--
Table: Runtime for various benchmarks, in milliseconds. Lower is better. "N/A" if error or more than 10 seconds. {#tab:benchmark}

| Benchmark       | jaq-2.0 | jq-1.7.1 | gojq-0.12.16 |
|-----------------|--------:|---------:|-------------:|
| `empty`         |     300 |      500 |      **230** |
| `bf-fib`        | **440** |     1230 |          570 |
| `defs`          |  **60** |      N/A |         1020 |
| `upto`          |   **0** |      470 |          460 |
| `reduce-update` |  **10** |      550 |         1340 |
| `reverse`       |  **40** |      690 |          280 |
| `sort`          | **110** |      530 |          630 |
| `group-by`      | **500** |     1920 |         1500 |
| `min-max`       | **210** |      320 |          260 |
| `add`           | **460** |      630 |         1300 |
| `kv`            | **110** |      150 |          230 |
| `kv-update`     | **130** |      540 |          470 |
| `kv-entries`    | **570** |     1150 |          730 |
| `ex-implode`    | **520** |     1110 |          580 |
| `reduce`        | **770** |      890 |          N/A |
| `try-catch`     | **290** |      320 |          370 |
| `repeat`        | **140** |      840 |          530 |
| `from`          | **320** |     1010 |          590 |
| `last`          |  **40** |      240 |          110 |
| `pyramid`       | **340** |      350 |          480 |
| `tree-contains` |  **70** |      610 |          210 |
| `tree-flatten`  |     780 |      360 |       **10** |
| `tree-update`   | **700** |      970 |         1340 |
| `tree-paths`    |     440 |  **280** |          870 |
| `to-fromjson`   |  **40** |      360 |          110 |
| `ack`           | **520** |      710 |         1220 |
| `range-prop`    |     360 |      320 |      **230** |
| `cumsum`        | **280** |      380 |          450 |
| `cumsum-xy`     | **430** |      470 |          710 |

@tab:benchmark measures the runtime of jaq, `jq`, and gojq
on a set of 29 benchmarks.^[
  Instructions on how to evaluate the benchmarks are given in jaq's `README.md`.
]
The benchmarks were run on a Linux system with an AMD Ryzen 5 5500U.
The number for the best performance (lowest runtime) is marked as bold.
The results show that
jaq-2.0 is fastest on 25 benchmarks, whereas
jq-1.7.1 is fastest on 1 benchmark and
gojq-0.12.16 is fastest on 3 benchmarks.

Several of the benchmarks measure the performance of update operations,
as explained in @sec:updates.
The names of these benchmarks end with `-update`.
We can see that jaq is the fastest implementation for all update benchmarks.
The next section shows a more detailed updated benchmark that is not part of @tab:benchmark.
-->

## Update performance

We now compare the performance of
path-based updates (as used in `jq` and gojq) and
path-less updates (as used in jaq).
We evaluate on two different inputs:

- `[range(1000000)]`        (an array of the shape `[0, ..., 999999]`)
- `{"a": [range(1000000)]}` (an object of the shape `{"a": [0, ..., 999999]}`)

The second input allows us to measure the impact of updating nested data.
For both inputs, we evaluate the runtime of different actions,
in order to determine the cost of different kinds of updates:

- Construction: Only construct the input (identity function).
  This serves as baseline, because all actions include input construction.
- Native update: Update using the built-in update operator `|=`.
  On jaq, this uses path-less  updates, whereas
  on jq,  this uses path-based updates.
- Manual update: Update without `|=`.
- Path-based update: Update with `|=`,
  forcing the usage of paths as shown in @sec:pathless-updates.

Action            | `[range(1000000)]`        | `{"a": [range(1000000)]}`
----------------- | ------------------------- | -----------------------------
Construction      | `.`                       | `.`
Native update     | `.[] |= .`                | `.a[] |= .`
Manual update     | `[.[] | .]`               | `{a: .a | [.[] | .]}`
Path-based update | `getpath(path(.[])) |= .` | `getpath(path(.a[])) |= .`

Table: Evaluated filter `f` depending on input and action. \label{tab:update-eval}

The filters that correspond to each of these actions are given in @tab:update-eval.
Every update applies the identity function (`.`)
to all elements of the array contained in its input,
which means that they return output equal to the input.

We evaluate the runtime of input construction `i` and action `f` by
running `$JQ -n 'i | f | empty`.[^empty-avoid]
For example, to evaluate jaq's native update performance on array input,
we measure the time taken by
`jaq -n '[range(1000000)] | .[] |= . | empty'`.

[^empty-avoid]:
  The usage of `empty` is necessary to avoid printing the output,
  which can be very costly performance-wise.

\begin{figure}
\centering
\input{eval/update.tex}
\caption{Runtime to construct and process input. Lower is better.}
\label{fig:update}
\end{figure}

The results are given in @fig:update.
Consider the results for array input `[range(1000000)]`:
We can see that native update performance differs enormously between
`jq` and jaq:
When subtracting the time for input construction,
`jq` takes about fifty times (!) as long for the update as jaq.^[
$(2041 - 106) \div (114 - 73) = 47.20$
]
We can also see that in `jq` and gojq,
(path-based) native updates are significantly _slower_ than manual updates, whereas in jaq,
(path-less)  native updates are _faster_ than manual updates.
Finally, we can see that when forcing path-based updates,
the performance of jaq plummets, arriving
at the same order of magnitude as `jq`'s and gojq's native updates.[^jq-path-force]
That indicates that `jq`'s and gojq's low update performance is caused by path-based updates.

[^jq-path-force]:
  When forcing path-based updates in `jq` and gojq via `getpath(path(...)) |= ...`,
  the performance also decreases compared to its (path-based) native updates.
  That is because in this scenario, `jq` and gojq evaluate each path twice, namely
  a first time via `|=` and a second time via `getpath(path(..))`.

Now, let us look at the results for object input `{"a": [range(1000000)]}`,
in order to study the performance of nested updates, namely
updating all values of an array inside an object.
First, we can observe that the performance of manual updates in `jq`, gojq, and jaq,
as well as native update performance in jaq, remain stable.
That means that these kinds of updates are not impacted by nesting.
On the other hand, the performance of path-based updates clearly decreases.

To sum it up:
Path-based updates are significantly slower than
manually updating data without the `|=` operator.
Furthermore, path-based update performance is impacted negatively by nesting.
However, updates can be made to achieve higher performance than manual updates,
by using our path-less update semantics.
