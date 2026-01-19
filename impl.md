# Implementation {#sec:impl}

We have created an interpreter for the jq language called `jaq`
based on the semantics in @sec:semantics.
`jaq` is written in Rust and can execute sufficiently large and complex jq programs such as
a Brainfuck interpreter and
a jq interpreter written in the jq language itself [@jqjq].
In practice,
the differences between our new semantics and the semantics implemented by `jq`
can often be neglected.

The other main implementations of the jq language, namely `jq` and `gojq`,
both compile jq programs to a list of imperative instructions and execute it, whereas
`jaq` compiles jq programs to an abstract syntax tree and interprets it.

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

@tab:benchmark measures the runtime of `jaq`, `jq`, and `gojq`
on a set of 29 benchmarks.^[
  Instructions on how to evaluate the benchmarks are given in `jaq`'s `README.md`.
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
We can see that `jaq` is the fastest implementation for all update benchmarks.
Let us have a look at a simple update benchmark that is not part of @tab:benchmark.

Table: Filter runtime in milliseconds with input 1000000. Lower is better. {#tab:update-bench}

| Filter | jaq-2.0 | jq-1.7.1 | gojq-0.12.16 |
| ------ | ------- | -------- | ------------ |
| `[range(.)]`              | **44** | 159 | 178 |
| `[range(.)] |  .[] += 1`  | **97** |1873 |1030 |
| `[range(.)] | [.[] +  1]` |**196** | 307 | 401 |

::: {.example name="Update performance"}
  Given an input number `n`, the filter
  `[range(.)]` constructs an array `[0, 1, ..., n-1]`.
  We can benchmark a jq implementation `$JQ`
  (where `$JQ` is either `jaq`, `jq`, or `gojq`) by
  `time $JQ '[range(.)] | length' <<< 1000000`.
  Here, we pipe the array output through `length` such that
  only the length of the output array is printed,
  in order not to measure the runtime for printing the whole array.
  The results are given in @tab:update-bench and shall serve as baseline.

  Next, we consider the filter `[range(.)] | .[] += 1`, where
  `.[] += 1` increments all elements of its input array by one.
  By subtracting
  the time needed to run `[range(.)]` from
  the time needed to run `[range(.)] | .[] += 1`,
  we can infer the time spent to perform the update operation `.[] += 1`, namely
  55ms (= 97ms - 44ms) for jaq,
  1714ms for jq, and
  852ms for gojq.
  Here, jaq is
  about 15 times faster than gojq and
  about 31 times faster than jq!

  Another program that performs the same task as the previous one can be obtained by
  replacing `.[] += 1` with `[.[] + 1]`:
  The latter iterates over all values of the array with `.[]`,
  adds one to all values, then creates a new array from the resulting values.
  We now have much closer results for the different implementations.
  Here, jq and gojq are faster than before because
  they  do not generate paths corresponding to `.[]` for `[.[] + 1]`, whereas
  they _do_    generate paths corresponding to `.[]` for `.[] += 1`.
  This shows the high cost of path-based updates, which
  our new update semantics --- and thus jaq --- avoid.
:::

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
\input{eval/update.tex}
\caption{Runtime to construct and process input. Lower is better.}
\label{fig:update}
\end{figure}

We evaluate the runtime of input construction `i` and action `f` by
running `$JQ -n 'i | f | empty`.[^empty-avoid]
For example, to evaluate jaq's native update performance on array input,
we measure the time of
`jaq -n '[range(1000000)] | .[] |= . | empty`.

[^empty-avoid]:
  The usage of `empty` is necessary to avoid printing the output,
  which can be very costly performance-wise.

The results are given in @fig:update.
Let us first look at the results for array input `[range(1000000)]`.
We can see that native update performance differs enormously between
jq and jaq:
When subtracting the time for input construction,
<!-- (2043−107)÷(113−74) = 49.64 -->
jq takes about fifty times (!) as long for the update as jaq.
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
as well as the performance of native update in jaq, remains stable.
That means that these kinds of updates are not impacted by nesting.
On the other hand, the performance of path-based updates clearly decreases.

To sum it up:
Path-based updates are significantly slower than
manually updating data without the `|=` operator.
Furthermore, path-based update performance is impacted negatively by nesting.
However, updates can be made to achieve higher performance than manual updates,
by using our path-less update semantics.
