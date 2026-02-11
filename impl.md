# Implementation {#sec:impl}

We implemented two interpreters for the jq language, namely ujq and jaq.
ujq is a minimalistic research interpreter that
demonstrates that our semantics can be implemented _compactly_.
jaq is a full-featured interpreter that
demonstrates that our semantics can also be implemented _efficiently_.
jaq's user base allows us to estimate whether
users are impacted by differences between our semantics and actual `jq` behaviour.
This is particularly interesting for the update semantics,
where our semantics diverge most notably from `jq`.


## ujq

ujq is a translation of this paper's contents to Haskell,
aiming to provide an minimal executable version of this paper.
In particular, ujq implements
lowering of a jq filter to IR (@sec:ir) and
execution of an IR filter (@sec:semantics).
@sec:ujq explains in more detail how ujq relates to our semantics.




## jaq

jaq is a full-featured jq interpreter written in Rust.
Like ujq, jaq implements the semantics in @sec:semantics, however,
it adds a number of optimisation techniques, such as tail-call optimisation (TCO).
That makes it more difficult to establish by looking at the code that jaq implements our semantics,
however, this can be tested experimentally by comparing outputs of ujq and jaq.
Furthermore, jaq not only implements the core jq language,
but also a substantial part of jq's standard library.
It demonstrates that the semantics can be implemented efficiently.

jaq can execute sufficiently large and complex jq programs such as
interpreters written in jq for various programming languages, including
Whitespace (`wsjq`),
Brainfuck, and
jq (`jqjq`) [@jqjq].

The other main implementations of the jq language, namely `jq` and gojq,
both compile jq programs to a list of imperative instructions and execute it, whereas
jaq compiles jq programs to an abstract syntax tree and interprets it.

\begin{figure}
\centering
\input{eval/interpreters.tex}
\caption{Runtime to .... Lower is better.}
\label{fig:interpreters}
\end{figure}

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

We now compare the performance of path-based updates (as used in jq) and
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
- Path-based update: Update with `|=`, forcing the usage of paths.

The filters that correspond to each of these actions are given in @tab:update-eval.
Every update applies the identity function (`.`)
to all elements of the array contained in its input,
which means that they return output equal to the input.

Action            | `[range(1000000)]`        | `{"a": [range(1000000)]}`
----------------- | ------------------------- | -----------------------------
Construction      | `.`                       | `.`
Native update     | `.[] |= .`                | `.a[] |= .`
Manual update     | `[.[] | .]`               | `{a: .a | [.[] | .]}`
Path-based update | `getpath(path(.[])) |= .` | `getpath(path(.a[])) |= .`

Table: Evaluated filter `f` depending on input and action. \label{tab:update-eval}

\begin{figure}
\centering
\input{eval/update.tex}
\caption{Runtime to construct and process input. Lower is better.}
\label{fig:update}
\end{figure}

We evaluate the runtime of input construction `i` and action `f` by
running `$JQ -n 'i | f | empty`.[^empty-avoid]
For example, to evaluate jaq's native update performance on array input,
we measure the time taken by
`jaq -n '[range(1000000)] | .[] |= . | empty'`.

[^empty-avoid]:
  The usage of `empty` is necessary to avoid printing the output,
  which can be very costly performance-wise.

The results are given in @fig:update.
Let us first look at the results for array input `[range(1000000)]`.
We can see that native update performance differs enormously between
jq and jaq:
When subtracting the time for input construction,
jq takes about fifty times (!) as long for the update as jaq.^[
$(2043 - 107) \div (113 - 74) = 49.64$
]
We can also see that in jq,
(path-based) native updates are significantly _slower_ than manual updates, whereas in jaq,
(path-less)  native updates are _faster_ than manual updates.
Finally, we can see that when forcing path-based updates,
the performance of jaq plummets, arriving
at the same order of magnitude as jq's native updates.[^jq-path-force]
That indicates that jq's low update performance is caused by path-based updates.

[^jq-path-force]:
  When forcing path-based updates in jq via `getpath(path(...)) |= ...`,
  the performance also decreases compared to its (path-based) native updates.
  That is because in this scenario, jq evaluates each path twice, namely
  a first time via `|=` and a second time via `getpath(path(..))`.

Now, let us look at the results for object input `{"a": [range(1000000)]}`,
in order to study the performance of nested updates, namely
updating all values of an array inside an object.
First, we can observe that the performance of manual updates in both jq and jaq,
as well as native update performance in jaq, remain stable.
That means that these kinds of updates are not impacted by nesting.
On the other hand, the performance of path-based updates clearly decreases.

To sum it up:
Path-based updates are significantly slower than
manually updating data without the `|=` operator.
Furthermore, path-based update performance is impacted negatively by nesting.
However, updates can be made to achieve higher performance than manual updates,
by using our path-less update semantics.

## Compatibility

Via jaq's issue tracker, we can estimate the impact of incompatibility.
This is particularly useful for our path-less update semantics.
<!-- https://github.com/01mf02/jaq/pull/285 -->
Users reported three issues caused by the update semantics described in this paper;
these were all duplicates about the semantics of `.. |= g`.
As explained in @ex:rec-update, our original semantics caused infinite loops,
and we have since adjusted our semantics to address this issue.
The fact that there were three independent reports of
the same issue related to update semantics shows that users
extensively use update semantics in jaq and
report issues they have with it.
The fact that no other issues with update semantics were opened so far
indicates that our new update semantics do not cause
incompatibility concerns for a vast majority of users.
