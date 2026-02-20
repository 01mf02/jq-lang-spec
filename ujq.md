# Comparison between ujq and our semantics {#sec:ujq}

ujq implements a value type that is quite close to JSON, as well as
the operations given in @sec:values.
However, the operations implemented in ujq are quite simplified and
do not support all functionalities of their counterparts in `jq`;
for example,
`jq` supports the division of two strings, whereas
ujq yields a runtime error in that case.
Implementing all value operations like in `jq` would add a lot of code to ujq,
without deepening our understanding of the core semantics.
The feasibility of implementing more complete value operations
within the framework established in @sec:values is demonstrated by jaq.

There is one main difference between ujq and the semantics in this paper:
In our semantics, compilation transforms an IR filter into
a lambda term that can be readily executed.
This compilation involves the construction of lambda terms with unbound variables,
which relies on wellformedness (@sec:wf) to ensure that
the final result is a closed term.
However, in Haskell, we cannot construct functions with unbound variables.
Therefore, ujq carries along a _context_ that
holds the currently assigned values to variables, filters, and break labels.^[
  We have also considered using an explicit context in this paper instead, but
  we found that this complicates presentation, while adding little to comprehension.
]
Furthermore, ujq _interprets_ IR filters, which is equivalent to
performing the compilation step in this paper
whenever a part of a filter is executed.

Despite these differences, we can still relatively easily see
the equivalence between our formal semantics and ujq.
To this end, we show
an excerpt of our evaluation semantics in @tab:eval-excerpt and
the corresponding implementation in ujq:

~~~ haskell
run :: Value v => Filter -> Ctx v -> ValP v -> [ValPR v]
run f c@Ctx{vars} vp = case f of
  Id -> [ok vp]
  Var x -> [ok $ newVal $ vars ! x]
  Concat f g -> run f c vp ++ run g c vp
  Compose f g -> run f c vp `bind` run g c
  Bind f x g -> run f c vp `bind` (\y -> run g (bindVar x (val y) c) vp)
~~~

Table: Evaluation semantics (excerpt of @tab:eval-semantics). {#tab:eval-excerpt}

| $\varphi$ | $\run\, \sem \varphi\, v$ |
| --------- | ------------------------- |
| $.$ | $\stream{\ok v}$ |
| $\$x$ | $\stream{\ok \$x}$ |
| $f, g$ | $\run\, \sem f\, v + \run\, \sem g\, v$ |
| $f | g$ | $\run\, \sem f\, v \bind \run\, \sem g$ |
| $f \jqas \$x | g$ | $\run\, \sem f\, v \bind (\lambda \$x. \run\, \sem g\, v)$ |

This code shows the evaluation of the filters
$.$ (identity),
`$x` (variable),
$f, g$ (concatenation),
$f | g$ (composition), and
$f \jqas \$x | g$ (binding).
As mentioned above, ujq's `run` expects an additional context `c`, which is used
to obtain the value bound to a variable in the `Var` case (via `vars ! x`) and
to bind a variable to a value in the `Bind` case (via `bindVar`).
Furthermore, ujq explicitly performs conversions between values and value-paths,
which we do implicitly in the formal semantics, as explained in @sec:implicit-conversion.
The code performs these conversions with the functions
`newVal` in the `Var` case (convert a value to a value-path) and
`val` in the `Bind` case (convert a value-path to a path).

ujq implements the built-in filter `path/1`, to allow evaluating the paths returned by a filter.
