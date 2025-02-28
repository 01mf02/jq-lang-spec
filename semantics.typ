#import "common.typ": *

= Evaluation Semantics <semantics>

In this section, we will show how to transform --- or compile --- a filter $phi$ to a lambda term $[|phi|]$,
such that $"eval" [|phi|]$ is a function that takes an input value $v$ and returns
the list of values that the filter $phi$ outputs when given the input $v$.
The evaluation strategy is call-by-name.

== Compilation

We will use pairs to store two functions
--- a run and an update function --- that characterise each filter $cal(F)$.

$ "pair"&:           &&(cal(V) -> cal(L)) &&-> ((cal(V) -> cal(L)) -> cal(V) -> cal(L)) -> cal(F) &&:= lam(x, y, f)   app(f, x, y)  \
   "run"&: cal(F) -> &&(cal(V) -> cal(L)) &&                                                      &&:= lam(p) app(p, (lam(x, y) x)) \
   "upd"&: cal(F)    &&                   &&-> ((cal(V) -> cal(L)) -> cal(V) -> cal(L))           &&:= lam(p) app(p, (lam(x, y) y)) $

The lambda term $[|phi|]$ corresponding to a filter $phi$ that we will define
will always be a pair of two functions, namely a run and an update function.
It has the shape $ [|phi|] = app("pair", (lam(v) t_r), (lam(sigma, v) t_u)) $
for some terms $t_r$ (run function) and $t_u$ (update function).
We retrieve the two functions from a pair with the functions $"run"$ and $"upd"$.
For a given $phi$, we can obtain
$t_r$ by $app("run", [|phi|],        v)$ and
$t_u$ by $app("upd", [|phi|], sigma, v)$.
For conciseness, we write
$app("run", [|phi|],        v)$ to define $t_r$ and
$app("upd", [|phi|], sigma, v)$ to define $t_u$.
#example("Identity filter compilation")[
  For the identity filter "$.$", we have $ [|.|] = app("pair",
  (lam(v) stream(ok(v))),
  (lam(sigma, v) app(sigma, v))), $ where
  $t_r = stream(ok(v))$ was obtained from @tab:eval-semantics and
  $t_u = app(sigma, v)$ was obtained from @tab:update-semantics.
]

#let fresh = $kappa$

The lambda term $[|phi|]$ obtained from a well-formed filter $phi$
may contain at most one free variable, namely $fresh$.
This variable is used to generate fresh labels for the execution of
$"label" var(x) | f$, see @ex:labels.
In order to create a closed term, we initially bind $fresh$ to zero.
We can then run a filter using the following function:

$ "eval": cal(F) -> cal(V) -> cal(L) := lam(phi) app((lam(fresh) app("run", phi)), "zero") $

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $app("run", [|phi|], v)$,
  $.$, $stream(ok(v))$,
  $n "or" s$, $stream(ok(phi))$,
  $var(x)$, $stream(ok(var(x)))$,
  $[]$, $stream(ok("arr"_0))$,
  ${}$, $stream(ok("obj"_0))$,
  $[f]$, $stream("arr" (app("run", [|f|], v)))$,
  ${var(x): var(y)}$, $stream(app("obj"_1, var(x), var(y)))$,
  $var(x) arith var(y)$, $stream(var(x) arith var(y))$,
  $var(x) cartesian var(y)$, $stream(ok((var(x) cartesian var(y))))$,
  $f, g$, $app("run", [|f|], v) + app("run", [|g|], v)$,
  $f | g$, $app("run", [|f|], v) bind app("run", [|g|])$,
  $f alt g$, $app((lam(t) app(t, (lam(\_, \_) t), (app("run", [|g|], v)))), (app("run", [|f|], v) bind "trues"))$,
  $f "as" var(x) | g$, $app("run", [|f|], v) bind (lam(var(x)) app("run", [|g|], v))$,
  $"try" f "catch" g$, $app("run", [|f|], v) bindl lam(r) app(r, (lam(o) stream(r)), (app("run", [|g|])), (lam(b) stream(r)))$,
  $"label" var(x) | f$, $app("label", fresh, (app((lam(var(x), fresh) app("run", [|f|], v)), fresh, (app("succ", fresh)))))$,
  $"break" var(x)$, $stream(app("break", var(x)))$,
  $"if" var(x) "then" f "else" g$, $app("run", (app((app("bool", var(x))), [|f|], [|g|])), v)$,
  $.[p]^?$, $v[p]^?$,
  $"reduce" x "as" var(x) (.; f)$, $app("reduce", (lam(var(x)) app("run", [|f|])), (app("run", [|x|], v)), v)$,
  $"foreach" x "as" var(x) (.; f; g)$, $app("foreach", (lam(var(x)) app("run", [|f|])), (lam(var(x)) app("run", [|g|])), (app("run", [|x|], v)), v)$,
  $"def" x(x_1; ...; x_n) defas f defend g$, $(lam(x) app("run", [|g|], v)) (app(Y_(n+1), (lam(x, x_1, ..., x_n) [|f|])))$,
  $x(f_1; ...; f_n)$, $app("run", (app(x, [|f_1|], ..., [|f_n|])), v)$,
  $f update g$, $app("upd", [|f|], (app("run", [|g|])), v)$,
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss its different cases:

- "$.$": Returns its input value. This is the identity filter.
- $n$ or $s$: Returns the value corresponding to the number $n$ or string $s$.
- $var(x)$: Returns the value currently bound to the variable $var(x)$.
  Wellformedness of the filter (as defined in @mir) ensures that
  whenever we evaluate $var(x)$, it must have been substituted,
  for example by a surrounding call to $f "as" var(x) | g$.
- $[]$ or ${}$: Creates an empty array or object.
- $[f]$: Creates an array from the output of $f$, using the function $"arr"$ defined in @values.
- ${var(x): var(y)}$: Creates an object from the values bound to $var(x)$ and $var(y)$,
  using the function $"obj"_1$ defined in @values.
- $var(x) arith var(y)$: Returns the output of an arithmetic operation "$arith$"
  (any of $+$, $-$, $times$, $div$, and $mod$, as given in @tab:binops)
  on the values bound to $var(x)$ and $var(y)$.
- $var(x) cartesian var(y)$: Returns the output of a Boolean operation "$cartesian$"
  (any of $eq.quest$, $eq.not$, $<$, $<=$, $>$, $>=$, as given in @tab:binops)
  on the values bound to $var(x)$ and $var(y)$.
  Because we assumed that Boolean operations return $cal(V)$ and are thus infallible
  (unlike the arithmetic operations $arith$, which return $cal(R)$),
  we have to wrap their outputs with an $"ok"$.
- $f, g$: Concatenates the outputs of $f$ and $g$, both applied to the same input.
- $f | g$: Composes $f$ and $g$, returning the outputs of $g$ applied to all outputs of $f$.
- $f alt g$: Let $l$ be the outputs of $f$ whose boolean values are not false.
  This filter returns $l$ if $l$ is not empty, else the outputs of $g$.
  Here, we use a function $app("trues", x)$ that
  returns its input $x$ if its boolean value is true.
$ "trues": cal(V) -> cal(L) := lam(x) app((app("bool", x)), stream(app("ok", x)), stream()) $
- $f "as" var(x) | g$: For every output of $f$, binds it to the variable $var(x)$ and
  returns the output of $g$, where $g$ may reference $var(x)$.
  Unlike $f | g$, this runs $g$ with the original input value instead of an output of $f$.
  We can show that the evaluation of $f | g$ is equivalent to that of
  $f "as" var(x') | var(x') | g$, where $var(x')$ is a fresh variable.
  Therefore, we could be tempted to lower $f | g$ to
  $floor(f) "as" var(x') | var(x') | floor(g)$ in @tab:lowering,
  in order to further simplify MIR and thus the semantics.
  However, we cannot do this because we will see in @updates that
  this equivalence does _not_ hold for updates; that is,
  $(f | g) update sigma$ is _not_ equal to $(f "as" var(x') | var(x') | g) update sigma$.
- $"try" f "catch" g$: Replaces all outputs of $f$ that equal $app("err", e)$ for some $e$
  by the output of $g$ on the input $e$.
  At first sight, this seems to diverge from jq, which
  aborts the evaluation of $f$ after the first error.
  However, because lowering to MIR replaces
  $"try" f "catch" g$ with
  $"label" var(x') | "try" f "catch" (g, "break" var(x'))$ (see @tab:lowering),
  the overall behaviour described here corresponds to jq after all.
- $"label" var(x) | f$: Returns all values yielded by $f$ until $f$ yields
  an exception $app("break", var(x))$.
  This uses a function $"label"$ that
  takes a label $fresh$ and a list $l$ of value results,
  returning the longest prefix of $l$ that does not contain $app("break", fresh)$:
  $ "label"&: bb(N) -> cal(L) -> cal(L) \
         &:= lam(fresh, l) app(l, (lam(h, t) app((lam(c) app(h, (lam(o) c), (lam(e) c), (lam(b) app("nat_eq", fresh, b, stream(), c)))), (stream(h) + app("label", fresh, t)))), stream()) $
  In this function, $c$ gets bound to $stream(h) + app("label", fresh, t)$,
  which is the function output when the head $h$ is not equal to $app("label", fresh)$.
- $"break" var(x)$: Returns a value result $app("break", var(x))$.
  Similarly to the evaluation of variables $var(x)$ described above,
  wellformedness of the filter (as defined in @hir) ensures that
  the returned value $app("break", var(x))$ will be
  eventually handled by a corresponding filter
  $"label" var(x) | f$.
  That means that $"eval" [|phi|]$ for a wellformed filter $phi$ can only yield
  values and errors, but never a $"break"$ result.
- $"if" var(x) "then" f "else" g$: Returns the output of $f$ if $var(x)$ is bound to
  a "true" value (neither null nor false for JSON, see @simple-fns), else returns the output of $g$.
- $.[p]^?$: Accesses parts of the input value;
  see @value-ops for the definitions of the operators.
  When evaluating this, the indices contained in $p$ have been substituted by values.
- $fold x "as" var(x) (.; f)$: Folds $f$ over the values returned by $x$,
  starting with the current input as accumulator.
  The current accumulator value is provided to $f$ as input value and
  $f$ can access the current value of $x$ by $var(x)$.
  If $fold = "reduce" $, this returns only the final        values of the accumulator, whereas
  if $fold = "foreach"$, this returns also the intermediate values of the accumulator.
  We will further explain this and define the functions
  $app( "reduce", f,    l, v)$ and
  $app("foreach", f, g, l, v)$ in @folding.
- $"def" x(x_1; ...; x_n) defas f defend g$: Binds the $n$-ary filter $x$ in $g$.
  The definition of $x$, namely $f$, may refer to
  any of the arguments $x_i$ as well as to $x$ itself.
  In other words, filters can be defined recursively,
  which is why we use the Y combinator $Y_(n+1)$ here.
  @ex:recursion shows how a recursive call is evaluated.
- $x(f_1; ...; f_n)$: Calls an $n$-ary filter $x$.
  This also handles the case of calling nullary filters such as $"empty"$.
- $f update g$: Updates the input at positions returned by $f$ by $g$.
  We will discuss this in @updates.

An implementation may also define semantics for builtin named filters.
For example, an implementation may define
$app("run", [|"error"|], v) := stream(app("err", v))$ and
$app("run", [|"keys" |], v) := stream("arr" app("keys", v))$, see @simple-fns.
In the case of $"keys"$, for example, there is no obvious way to implement it by definition,
in particular because there is no simple way to obtain the domain of an object ${...}$
using only the filters for which we gave semantics in @tab:eval-semantics.

#example("Recursion")[
  Consider the following MIR filter $phi$: $"def" "repeat" defas ., "repeat" defend "repeat"$.
  This filter repeatedly outputs its input;
  for example, given the input $v = 1$, it returns $stream(ok(1), ok(1), ok(1), ...)$.
  First, let us compile a part of our filter, namely
  $ rho = [|., "repeat"|] =^[|dot.op|] app("pair", (lam(v) stream(ok(v)) + "run" "repeat" v), (...)). $
  Here, the second part of the pair $(...)$ does not matter, because
  it is never evaluated due to our not performing any updates in this example.

  Now, we can evaluate the filter $phi$ by
  $app("eval", [|phi|], v) = app((lam(fresh) app("run", [|phi|])), "zero", v) $.
  Because $phi$ does not contain any labels,
  $[|phi|]$ does not make any reference to $fresh$, therefore
  $app("eval", [|phi|], v)$ is equivalent to:
  $ app("run", [|phi|], v)
  &= app((lam("repeat") app("run", [|"repeat"|], v)), (app(Y_1, (lam("repeat") rho)))) \
  &=^[|dot.op|] app((lam("repeat") app("run", "repeat", v)), (app(Y_1, (lam("repeat") rho)))) \
  &=^beta app("run", (app(Y_1, (lam("repeat") rho))), v) \
  &=^(Y_1) app("run", (app((lam("repeat") rho), (app(Y_1, (lam("repeat") rho))))), v) \
  &=^rho app("run", (app((lam("repeat") app("pair", (lam(v) stream(ok(v)) + "run" "repeat" v), (...))), (app(Y_1, (lam("repeat") rho))))), v) \
  &=^beta app("run", (app("pair", (lam(v) stream(ok(v)) + app("run", (app(Y_1, (lam("repeat") rho))), v)), (...))), v) \
  &=^beta app(stream(ok(v)) + app("run", (app(Y_1, (lam("repeat") rho))), v)) \
  &= stream(ok(v)) + app("run", [|phi|], v). $
  This shows that the evaluation of $phi$ on any input $v$ yields
  an infinite stream of $ok(v)$ results.
] <ex:recursion>

#example("Labels")[
  Let us consider the filter $phi equiv "label" var(x) | "break" var(x)$.
  We have:
  $ app("eval", [|phi|], v)
  &= (lam(fresh) "run" [|"label" var(x) | "break" var(x)|]) "zero" v \
  &= (lam(fresh, v) app("label", fresh, (app((lam(var(x), fresh) app("run", [|"break" var(x)|], v)), fresh, ("succ" fresh))))) "zero" v \
  &= "label" "zero" ((lam(var(x), fresh) stream("break" var(x))) "zero" ("succ" "zero")) \
  &= "label" "zero" stream("break" "zero") \
  &= stream() $
  It is interesting to note that if instead of $"break" var(x)$,
  we would have used a more complex filter, e.g. $"label" var(y) | ...$,
  then $var(y)$ would have been substituted by $"succ" "zero"$
  (which we can already see in our large equation above).
  This mechanism reliably allows us to generate fresh labels and to
  differentiate for each $"break"$ the corresponding $"label"$ that handles it.
] <ex:labels>

/*
For $"length"$, we could give a definition, using
$"reduce" .[] "as" var(x) (0; . + 1)$ to obtain the length of arrays and objects, but
this would inherently require linear time to yield a result, instead of
constant time that can be achieved by a proper jq implementation.
*/

== Folding <folding>

In this subsection, we will define the functions
$"reduce"$ and $"foreach"$ which underlie the semantics for the folding operators
$"reduce"  x "as" var(x) (.; f)$ and
$"foreach" x "as" var(x) (.; f; g)$.

Let us start by defining a general folding function $"fold"$:
$ "fold"&: (cal(V) -> cal(V) -> cal(L)) -> (cal(V) -> cal(V) -> cal(L)) -> (cal(V) -> cal(L)) -> cal(L) -> cal(V) -> cal(L) \
        &:= lam(f, g, n) app(Y_2, (lam(F, l, v) app(l, (lam(h, t) app(f, h, v) bind (lam(y) app(g, h, y) + app(F, t, y))), (app(n, v))))) $
This function takes
two functions $f$ and $g$ that both take two values --- a list element and an accumulator --- and return a list of value results, and
a function $n$ (for the nil case) from a value $x$ to a list of value results.
From that, it creates a recursive function that
takes a list of value results $l$ and an accumulator value $v$ and
returns a list of value results.
This function folds over the elements in $l$, starting from the accumulator value $v$.
For every element $h$ in $l$,
$f$ is evaluated with $h$ and the current accumulator value $v$ as input.
Every output $y$ of $f$ is output after passing through $g$, then
used as new accumulator value with the remaining list $t$.
If $l$ is empty, then $v$ is called a _final_ accumulator value and $app(n, v)$ is returned.

We use two different functions for $n$;
the first returns just its input, corresponding to $"reduce"$ which returns a final value, and
the second returns nothing,  corresponding to $"foreach"$.
Instantiating $"fold"$ with these two functions, we obtain the following:

$ "reduce" &:= lam(f)     && app("fold", f, (lam(h, v) stream()), && (lam(v) stream(ok(v) &&))) \
  "foreach" &:= lam(f, g) && app("fold", f, g, && (lam(v) stream(&&))) $

Here, $"reduce"$ and $"foreach"$ are the functions used in @tab:eval-semantics.
Their types are:

$  "reduce"&: (cal(V) -> cal(V) -> cal(L)) &&-> cal(L) -> cal(V) -> cal(L) \
  "foreach"&: (cal(V) -> cal(V) -> cal(L)) -> (cal(V) -> cal(V) -> cal(L)) &&-> cal(L) -> cal(V) -> cal(L) $


We will now look at what the evaluation of the various folding filters expands to.
Assuming that the filter $x$ evaluates to $stream(x_0, ..., x_n)$,
then $"reduce"$ and $"foreach"$ expand to

$ "reduce"   x "as" var(x) (.; f   ) =& x_0 "as" var(x) | f & wide
  "foreach"  x "as" var(x) (.; f; g) =& x_0 "as" var(x) | f | g, ( \
|& ... &
 & ... \
|& x_n "as" var(x) | f &
 & x_n "as" var(x) | f | g, ( \
&&
 & "empty")...)
$

Note that jq implements only restricted versions of these folding operators
that consider only the last output of $f$ for the next iteration.
That means that in jq,
$"reduce" x "as" var(x) (.;         f)$ is equivalent to
$"reduce" x "as" var(x) (.; "last"(f))$.
Here, we assume that the filter $"last"(f)$
returns the last output of $f$ if $f$ yields any output, else nothing.



= Update Semantics <updates>

In this section, we will discuss how to evaluate updates $f update g$.
First, we will show how the original jq implementation executes such updates,
and show which problems this approach entails.
Then, we will give alternative semantics for updates that avoids these problems,
while enabling faster performance by forgoing the construction of temporary path data.

== jq updates via paths <jq-updates>

jq's update mechanism works with _paths_.
A path is a sequence of indices $i_j$ that can be written as $.[i_1]...[i_n]$.
It refers to a value that can be retrieved by the filter "$.[i_1] | ... | .[i_n]$".
Note that "$.$" is a valid path, referring to the input value.

The update operation "$f update g$" attempts to
first obtain the paths of all values returned by $f$,
then for each path, it replaces the value at the path by $g$ applied to it.
Note that $f$ is not allowed to produce new values; it may only return paths.

#example[
  Consider the input value $[[1, 2], [3, 4]]$.
  We can retrieve the arrays $[1, 2]$ and $[3, 4]$ from the input with the filter "$.[]$", and
  we can retrieve the numbers 1, 2, 3, 4 from the input with the filter "$.[] | .[]$".
  To replace each number with its successor, we run "$(.[] | .[]) update .+1$",
  obtaining $[[2, 3], [4, 5]]$.
  Internally, in jq, this first builds the paths
  $.[0][0]$, $.[0][1]$, $.[1][0]$, $.[1][1]$,
  then updates the value at each of these paths with $g$.
] <ex:arr-update>

This approach can yield surprising results when the execution of the filter $g$
changes the input value in a way that the set of paths changes midway.
In such cases, only the paths constructed from the initial input are considered.
This can lead to
paths pointing to the wrong data,
paths pointing to non-existent data, and
missing paths.

#example[
  Consider the input value ${qs(a) |-> {qs(b) |-> 1}}$ and the filter
  $(.[], .[][]) update g$, where $g$ is $[]$.
  Executing this filter in jq first builds the path
  $.[qs(a)]$ stemming from "$.[]$", then
  $.[qs(a)][qs(b)]$ stemming from "$.[][]$".
  Next, jq folds over the paths,
  using the input value as initial accumulator and
  updating the accumulator at each path with $g$.
  The final output is thus the output of $(.[qs(a)] update g) | (.[qs(a)][qs(b)] update g)$.
  The output of the first step $.[qs(a)] update g$ is ${qs(a) |-> []}$.
  This value is the input to the second step $.[qs(a)][qs(b)] update g$,
  which yields an error because
  we cannot index the array $[]$ at the path $.[qs(a)]$ by $.[qs(b)]$.
] <ex:obj-update-arr>

We can also have surprising behaviour that does not manifest any error.

#example[
  Consider the same input value and filter as in @ex:obj-update-arr,
  but now with $g$ set to ${qs(c): 2}$.
  The output of the first step $.[qs(a)] update g$ is ${qs(a) |-> {qs(c) |-> 2}}$.
  This value is the input to the second step $.[qs(a)][qs(b)] update g$, which yields
  ${qs(a) |-> {qs(c) |-> 2, qs(b) |-> {qs(c) |-> 2}}}$.
  Here, the remaining path ($.[qs(a)][qs(b)]$) pointed to
  data that was removed by the update on the first path,
  so this data gets reintroduced by the update.
  On the other hand, the data introduced by the first update step
  (at the path $.[qs(a)][qs(c)]$) is not part of the original path,
  so it is _not_ updated.
] <ex:obj-update-obj>

We found that we can interpret many update filters by simpler filters,
yielding the same output as jq in most common cases, but avoiding the problems shown above.
To see this, let us see what would happen if we would interpret
$(f_1, f_2) update g$ as $(f_1 update g) | (f_2 update g)$.
That way, the paths of $f_2$ would point precisely to the data returned by
$f_1 update g$, thus avoiding the problems depicted by the examples above.
In particular, with such an approach,
@ex:obj-update-arr would yield ${qs(a) |-> []}$ instead of an error, and
@ex:obj-update-obj would yield ${qs(a) |-> {qs(c) |-> {qs(c) |-> 2}}}$.

In the remainder of this section, we will show
semantics that extend this idea to all update operations.
The resulting update semantics can be understood to _interleave_ calls to $f$ and $g$.
By doing so, these semantics can abandon the construction of paths altogether,
which results in higher performance when evaluating updates.

== Properties of new semantics <update-props>

// μονοπάτι = path
// συνάρτηση = function
#figure(caption: [Update semantics properties.], table(columns: 2,
  $phi$, $phi update sigma$,
  $"empty"$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $"if" var(x) "then" f "else" g$, $"if" var(x) "then" f update sigma "else" g update sigma$,
  $f alt g$, $"if" "first"(f alt "null") "then" f update sigma "else" g update sigma$,
)) <tab:update-props>

@tab:update-props gives a few properties that we want to hold for updates $phi update sigma$.
Let us discuss these for the different filters $phi$:
- $"empty"$: Returns the input unchanged.
- "$.$": Returns the output of the update filter $sigma$ applied to the current input.
  Note that while jq only returns at most one output of $sigma$,
  these semantics return an arbitrary number of outputs.
- $f | g$: Updates at $f$ with the update of $sigma$ at $g$.
  This allows us to interpret
  $(.[] | .[]) update sigma$ in @ex:arr-update by
  $.[] update (.[] update sigma)$, yielding the same output as in the example.
- $f, g$: Applies the update of $sigma$ at $g$ to the output of the update of $sigma$ at $f$.
  We have already seen this at the end of @jq-updates.
- $"if" var(x) "then" f "else" g$: Applies $sigma$ at $f$ if $var(x)$ holds, else at $g$.
- $f alt g$: Applies $sigma$ at $f$ if $f$ yields some output whose boolean value (see @simple-fns) is not false, else applies $sigma$ at $g$.
  Here, $"first"(f)$ is a filter that returns
  the first output of its argument $f$ if there is one, else the empty list.

While @tab:update-props allows us to define the behaviour of several filters
by reducing them to more primitive filters,
there are several filters $phi$ which cannot be defined this way.
We will therefore give the actual update semantics of $phi update sigma$ in @new-semantics
by defining $app("upd", [|phi|], sigma, v)$, not
by translating $phi update sigma$ to equivalent filters.

== Limiting interactions <limiting-interactions>

To define $app("upd", [|phi|], sigma, v)$, we first have to understand
how to prevent unwanted interactions between $phi$ and $sigma$.
In particular, we have to look at variable bindings.

We can bind variables in $phi$; that is, $phi$ can have the shape $f "as" var(x) | g$.
Here, the intent is that $g$ has access to $var(x)$, whereas $sigma$ does not!
This is to ensure compatibility with jq's original semantics,
which execute $phi$ and $sigma$ independently,
so $sigma$ should not be able to access variables bound in $phi$.

#example[
  Consider the filter $0 "as" var(x) | phi update sigma$, where
  $phi$ is $(1 "as" var(x) | .[var(x)])$ and $sigma$ is $var(x)$.
  This updates the input array at index $1$.
  If $sigma$ had access to variables bound in $phi$,
  then the array element would be replaced by $1$,
  because the variable binding $0 "as" var(x)$ would be shadowed by $1 "as" var(x)$.
  However, in jq, $sigma$ does not have access to variables bound in $phi$, so
  the array element is replaced by $0$, which is the value originally bound to $var(x)$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.
]

We take the following approach to prevent variables bound in $phi$ to "leak" into $sigma$:
When evaluating $phi update sigma$, we want
$sigma$ to always be executed with the same variable bindings.
In order to ensure that, we define
$app("upd", [|phi|], sigma', v)$ not for a _filter_ $sigma$,
but for a _function_ $sigma': cal(V) -> cal(L)$, where
$app(sigma', x)$ returns the output of the filter $app("run", sigma, x)$.
This allows us to bind variables in $phi$ without impacting $sigma$.

== New semantics <new-semantics>

We will now give semantics that define the output of
$app("run", [|f update g|], v)$ as referred to in @semantics.

We will first combine the techniques in @limiting-interactions to define
$ app("run", [|f update g|], v) := app("upd", [|f|], sigma, v), "where"
  sigma: cal(V) -> cal(L) := app("run", [|g|]) $
We use the function $sigma$ instead of a filter on the right-hand side to
limit the scope of variable bindings as explained in @limiting-interactions.

#figure(caption: [Update semantics. Here, $phi$ is a filter and $sigma: cal(V) -> cal(L)$ is a function from a value to a list of value results.], table(columns: 2,
  $phi$, $app("upd", [|phi|], sigma, v)$,
  $.$, $app(sigma, v)$,
  $f | g$, $app("upd", [|f|], (app("upd", [|g|], sigma)), v)$,
  $f, g$, $app("upd", [|f|], sigma, v) bind app("upd", [|g|], sigma)$,
  $f alt g$, $app("upd", (app((app("run", [|f|], v) bind "trues"), (lam(\_, \_) [|f|]), [|g|])), sigma, v)$,
  $.[p]^?$, $stream(v[p]^? update sigma)$,
  $f "as" var(x) | g$, $app("reduce", (lam(var(x)) app("upd", [|g|], sigma)), (app("run", [|f|], v)), v)$,
  $"if" var(x) "then" f "else" g$, $app("upd", (app((app("bool", var(x))), [|f|], [|g|])), sigma, v)$,
  $"break" var(x)$, $stream(app("break", var(x)))$,
  $"reduce" x "as" var(x) (.; f)$, $app("reduce"_update, (lam(var(x)) app("upd", [|f|])), sigma, (app("run", [|x|], v)), v)$,
  $"foreach" x "as" var(x) (.; f; g)$, $app("foreach"_update, (lam(var(x)) app("upd", [|f|])), (lam(var(x)) app("upd", [|g|])), sigma, (app("run", [|x|], v)), v)$,
  $"def" x(x_1; ...; x_n) defas f defend g$, $(lam(x) app("upd", [|g|], sigma, v)) (app(Y_(n+1), (lam(x, x_1, ..., x_n) [|f|])))$,
  $x(f_1; ...; f_n)$, $app("upd", (app(x, [|f_1|], ..., [|f_n|])), sigma, v)$,
)) <tab:update-semantics>

@tab:update-semantics shows the definition of $app("upd", [|phi|], sigma, v)$.
Several of the cases for $phi$, like
"$.$", "$f | g$", "$f, g$", and "$"if" var(x) "then" f "else" g$"
are simply relatively straightforward consequences of the properties in @tab:update-props.
We discuss the remaining cases for $phi$:
- $f alt g$: Updates using $f$ if $f$ yields some non-false value, else updates using $g$.
  Here, $f$ is called as a "probe" first.
  If it yields at least one output that is considered "true"
  (see @semantics for the definition of $"trues"$),
  then we update at $f$, else at $g$.
  This filter is unusual because is the only kind where a subexpression may be both
  evaluated ($app("run", [|f|], v)$) as well as
  updated with ($app("upd", [|f|], sigma, v)$).
- $.[p]^?$: Applies $sigma$ to the current value at the path part $p$
  using the update operators in @value-ops.
- $f "as" var(x) | g$:
  Folds over all outputs of $f$, using the input value $v$ as initial accumulator and
  updating the accumulator by $g update sigma$, where
  $var(x)$ is bound to the current output of $f$.
  The definition of $"reduce"$ is given in @folding.
- $fold x "as" var(x) (.; f)$: Folds $f$ over the values returned by $var(x)$.
  We will discuss this in @folding-update.
- $"def" x(x_1; ...; x_n) defas f defend g$: Defines a filter.
  This is defined analogously to @tab:eval-semantics.
- $x(f_1; ...; f_n)$, $x$: Calls a filter.
  This is defined analogously to @tab:eval-semantics.

There are many filters $phi$ for which
$app("upd", [|phi|], sigma, v)$ is not defined,
for example $var(x)$, $[f]$, and ${}$.
In such cases, we assume that $app("upd", [|phi|], sigma, v)$ returns an error just like jq,
because these filters do not return paths to their input data.
Our update semantics support all kinds of filters $phi$ that are supported by jq, except for
$"label" var(x) | g$ and $"try" f "catch" g$.

#example("Update compilation")[
  Let us consider the filter $phi' equiv (.[] update .+.)$.
  When given an array as input, this filter outputs a new array where
  each value in the input array is replaced by the output of $.+.$ on the value.
  The filter $.+.$ returns the sum of the input and the input,
  effectively doubling its input.
  For example, when given the input $[1, 2, 3]$, the output of $phi$ is $[2, 4, 6]$.
  Before we can execute $phi'$, we have to convert it to MIR, e.g. to
  $phi equiv .[] update (. "as" var(x) | var(x) + var(x))$.#footnote[
    Note that $floor(phi') = (.[] update (. "as" var(x) | . "as" var(y) | var(x) + var(y)))$ is a bit longer than the $phi$ given here, but
    because the two are semantically equivalent, we continue with $phi$.
  ]
  Let us now trace the execution of the filter, namely
  $app("eval", [|phi|], v) = app((lam(fresh) app("run", [|phi|])), "zero", v)$.
  Because $phi$ does not use any labels,
  this is equivalent to just $app("run", [|phi|], v) = app("upd", [|(.[])|], sigma, v) = (v[] update sigma)$.
  Here, we introduced $sigma equiv app("run", [|. "as" var(x) | var(x) + var(x)|])$.
  We can further expand $sigma$:
  $ sigma &= lam(v) app("run", [|. "as" var(x) | var(x) + var(x)|], v) \
  &= lam(v) app("run", [|.|]) bind (lam(var(x)) app("run", [|var(x) + var(x)|], v)) \
  &= lam(v) stream(ok(v)) bind (lam(var(x)) stream(var(x) + var(x))) \
  &= lam(v) stream(v + v) $
  In summary, $"eval" [|phi|] v = (v[] update (lam(v) stream(v + v)))$.
]

#example("The Curious Case of Alternation")[
  The semantics of $(f alt g) update sigma$ can be rather surprising:
  For the input
  ${qs(a) |-> "true"}$, the filter
  $(oat(a) alt oat(b)) update 1$ yields
  ${qs(a) |-> 1}$.
  This is what we might expect, because the input has an entry for $qs(a)$.
  Now let us evaluate the same filter on the input
  ${qs(a) |-> "false"}$, which yields ${qs(a) |-> "false", qs(b) |-> 1}$.
  Here, while the input still has an entry for $qs(a)$ like above,
  its boolean value is _not_ true, so $oat(b) update 1$ is executed.
  In the same spirit, for the input ${}$ the filter yields ${qs(b) |-> 1}$,
  because $oat(a)$ yields $"null"$ for the input,
  which also has the boolean value $"false"$, therefore $oat(b) update 1$ is executed.

  For the input
  ${}$, the filter
  $("false" alt oat(b)) update 1$ yields
  ${qs(b) |-> 1}$.
  This is remarkable insofar as $"false"$ is not a valid path expression
  because it returns a value that does not refer to any part of the original input,
  yet the filter does not return an error.
  This is because
  $"false"$ triggers $oat(b) update 1$, so
  $"false"$ is never used as path expression.
  However, running the filter $("true" alt oat(b)) update 1$
  _does_ yield an error, because
  $"true"$ triggers $"true" update 1$, and
  $"true"$ is not a valid path expression.

  Finally, on the input
  $[]$, the filter
  $(.[] alt "error") update 1$ yields
  $stream(app("err", []))$.
  That is because $.[]$ does not yield any value for the input,
  so $"error" update 1$ is executed, which yields an error.
]

== Folding <folding-update>

In @folding, we have seen how to evaluate folding filters of the shape
$"reduce" x "as" var(x) (.; f)$ and
$"foreach" x "as" var(x) (.; f; g)$.
Here, we will define update semantics for these filters.
These update operations are _not_ supported in jq 1.7; however,
we will show that they arise quite naturally from previous definitions.

Let us start with an example to understand folding on the left-hand side of an update.

#example[
  Let $v = [[[2], 1], 0]$ be our input value
  and $phi$ be the filter $fold (0, 0) "as" var(x) (.; .[var(x)])$.
  The regular evaluation of $phi$ with the input value as described in @semantics yields
  $ app("run", [|phi|], v) = cases(
    stream(#hide($[[2], 1], $) [2]) & "if" fold = "reduce",
    stream(       [[2], 1],    [2]) & "if" fold = "foreach",
  ) $
  When $fold = "foreach"$, the paths corresponding to the output are $.[0]$ and $.[0][0]$, and
  when $fold = "reduce"$, the paths are just $.[0][0]$.
  Given that all outputs have corresponding paths, we can update over them.
  For example, taking $. + [3]$ as filter $sigma$, we should obtain the output
  #let h3 = hide($, 3$)
  $ app("upd", [|phi|], (app("run", [|sigma|])), v) = cases(
    stream([[[2, 3], 1#h3], 0]) & "if" fold = "reduce",
    stream([[[2, 3], 1, 3], 0]) & "if" fold = "foreach",
  ) $
] <ex:folding-update>

First, note that for folding filters,
the lowering in @tab:lowering and
the defining equations in @folding
only make use of filters for which we have already introduced update semantics in @tab:update-semantics.
This should not be taken for granted; for example, we originally lowered
$fold f_x "as" var(x) (f_y; f)$ to
$ floor(f_y) "as" var(y) | fold floor(f_x) "as" var(x) (var(y); floor(f)) $
instead of the more complicated lowering found in @tab:lowering, namely
$ . "as" var(x') | floor(f_y) | fold floor(var(x') | f_x) "as" var(x) (.; floor(f)). $
While both lowerings produce the same output for regular evaluation,
we cannot use the original lowering for updates, because the defining equations for
$fold x "as" var(x) (var(y); f)$ would have the shape $var(y) | ...$,
which is undefined on the left-hand side of an update.
However, the lowering in @tab:lowering avoids this issue
by not binding the output of $f_y$ to a variable,
so it can be used on the left-hand side of updates.

To obtain an intuition about how the update evaluation of a fold looks like, we can take
$fold x "as" var(x) (.; f; g) update sigma$,
substitute the left-hand side by the defining equations in @folding and
expand everything using the properties in @update-props.
This yields
$ "reduce"  x "as" var(x) (.; f   ) update sigma
=& x_0 "as" var(x) | (f update ( \
 & ... \
 & x_n "as" var(x) | (f update (  \
 & sigma))...)) \
  "foreach" x "as" var(x) (.; f; g) update sigma
=& x_0 "as" var(x) | (f update ((g update sigma) | \
 & ... \
 & x_n "as" var(x) | (f update ((g update sigma) | \
 & .))...)).
$

#example[
  To see the effect of above equations, let us reconsider
  the input value and the filters from @ex:folding-update.
  Using some liberty to write $.[0]$ instead of $0 "as" var(x) | .[var(x)]$, we have:
  #let hs = hide($sigma | ($)
  $ phi update sigma = cases(
    .[0] update #hs      .[0] update sigma   & "if " fold = "reduce",
    .[0] update sigma | (.[0] update sigma)  & "if " fold = "foreach",
  ) $
]

We will now formally define the functions used in @tab:update-semantics.
For this, we first introduce a function $"fold"_update$,
as counterpart to the function $"fold"$ in @folding.
Its first argument is of type $cal(V) -> (cal(V) -> cal(L)) -> cal(V) -> cal(L)$, which we abbreviate as $cal(U)$:

$ "fold"_update&: cal(U) -> (cal(V) -> cal(V) -> cal(L)) -> (cal(V) -> cal(L)) -> cal(L) -> cal(V) -> cal(L) \
               &:= lam(f, g, n) app(Y_2, (lam(F, l, v) app(l, (lam(h, t) app(f, h, (lam(x) app(g, h, x) bind app(F, t)), v)), (app(n, v))))) $

Using this function, we can now define

$  "reduce"_update &:= lam(f,    &&sigma) app("fold"_update, f, (lam(h, v) stream(ok(v))), && sigma) \
  "foreach"_update &:= lam(f, g, &&sigma) app("fold"_update, f, (lam(h, v) app(g, h, sigma, v)), && (lam(v) stream(ok(v)))) $

The types of the functions are:

$  "reduce"_update&: cal(U)           &&-> (cal(V) -> cal(L)) -> cal(L) -> cal(V) -> cal(L) \
  "foreach"_update&: cal(U) -> cal(U) &&-> (cal(V) -> cal(L)) -> cal(L) -> cal(V) -> cal(L) $
