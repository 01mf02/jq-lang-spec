#import "common.typ": *

= Evaluation Semantics <semantics>

In this section, we will show how to transform a filter $phi$ to a lambda term $[|phi|]$,
such that $[|phi|]$ is a function that takes an input value $v$ and returns
the stream of values that the filter $phi$ outputs when given the input $v$.
The evaluation strategy is call-by-name.

== Runtime

#let bind = $>#h(-0.5em)>#h(-1em / 6)=$
#let bindl = $class("binary", bind_L)$

We model streams using a standard representation of lists in lambda calculus:
$ "cons" &= lam(h, t, c, n) app(c, h, t) \
  "nil"  &= lam(c, n) n $

Furthermore, we introduce result values, which are either
OK or an exception (an error or a break):

$ "ok"    &= lam(x, o, e, b) app(o, x) \
  "err"   &= lam(x, o, e, b) app(e, x) \
  "break" &= lam(x, o, e, b) app(b, x) $

Next, we define pairs, which we use to store two functions
--- a run and an update function --- for each filter.
We retrieve the latter by $"run" := "fst"$ and $"upd" := "snd"$.

$ "pair" &= lam(x, y, f) app(f, x, y) \
  "fst"  &= lam(x, y). x \
  "snd"  &= lam(x, y). y $


We assume the existence of a set of Y combinators $Y_n$ that we will use to
define recursive functions of arity $n$.
For each $n$, we have that $Y_n f = f (Y_n f)$ holds.
Furthermore, the types of $Y_n$ are:

$ Y_1:& ((x_1 &&-> y) -> x_1 &&-> y) -> x_1 &&-> y \
  ... \
  Y_n:& ((x_1 -> ... -> x_n &&-> y) -> x_1 -> ... -> x_n &&-> y) -> x_1 -> ... -> x_n &&-> y $

The concatenation of two lists $l$ and $r$ can be defined as
$ l + r := app(Y_1, (lam(f, l) app(l, (lam(h, t) app("cons", h, (app(f, t)))), r)), l), $
which satisfies the equational property
$ l + r = app(l, (lam(h, t) app("cons", h, (t + r))), r). $
For simplicity, we will define recursive functions from here on mostly by equational properties,
from which we could easily derive proper definitions using the $Y_n$ combinators.

We use the monadic bind operator $bind$ to model composition.
For a list $l$ and a function $f$ from a list element to a list, we have
$ (l &bindl& f) &= app(l, (lam(h, t) app(f, h) + (t bindl f)), "nil") \
  (l &bind & f) &= l bindl (lam(x) app(x, (lam(o) app(f, o)), (lam(e) stream(x)), (lam(b) stream(x)))) $

Next, we define a function that is used to define alternation.
$app("trues", x)$ returns its input $x$ if its boolean value is true.
$ "trues" := lam(x) app((app("bool", x)), stream(app("ok", x)), "nil") $

#let ok(x) = $app("ok", #x)$

== Compilation

The lambda term $[|phi|]$ corresponding to a filter $phi$ that we will define
will always be a pair of two functions, namely a run and an update function.
It has the shape $ [|phi|] = app("pair", (lam(l, v) t_r), (lam(sigma, l, v) t_u)) $
for some terms $t_r$ (run function) and $t_u$ (update function).
For a given $phi$, we can obtain
$t_r$ by $app("run", [|phi|], l, v)$ and
$t_u$ by $app("upd", [|phi|], sigma, l, v)$.
For conciseness, we write
$app("run", [|phi|], l, v)$ to define $t_r$ and
$app("upd", [|phi|], sigma, l, v)$ to define $t_u$.
For example, if $phi = .$ (the identity filter), then $ [|phi|] = app("pair",
(lam(l, v) stream(ok(v))),
(lam(sigma, l, v) app(sigma, v))). $
// TODO: to run or not to run, that's the question!

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $app("run", [|phi|], l, v)$,
  $.$, $stream(ok(v))$,
  $n "or" s$, $stream(ok(phi))$,
  $[f]$, $stream([ app("run", [|f|], l, v) ])$,
  ${}$, $stream(ok({}))$,
  ${var(x): var(y)}$, $stream(ok({var(x): var(y)}))$,
  $var(x) cartesian var(y)$, $stream(ok((var(x) cartesian var(y))))$,
  $f, g$, $app("run", [|f|], l, v) + app("run", [|g|], l, v)$,
  $f | g$, $app("run", [|f|], l, v) bind app("run", [|g|], l)$,
  $f alt g$, $app((lam(t) app(t, (lam(\_, \_) t), (app("run", [|g|], l, v)))), (app("run", [|f|], l, v) bind "trues"))$,
  $f "as" var(x) | g$, $app("run", [|f|], l, v) bind (lam(var(x)) app("run", [|g|], l, v))$,
  $"try" f "catch" g$, $app("run", [|f|], l, v) bindl lam(r) app(r, (lam(o) stream(r)), (app("run", [|g|], l)))$,
  $"label" var(x) | f$, $app("label", l, (app((lam(var(x)) app("run", [|f|], (app("succ", l)), v)), l)))$,
  $"break" var(x)$, $stream(app("break", var(x)))$,
  $"if" var(x) "then" f "else" g$, $app("run", (app((app("bool", var(x))), [|f|], [|g|])), l, v)$,
  // TODO?
  $.[p]^?$, $v[p]^?$,
  $"reduce" x "as" var(x) (.; f)$, $app("reduce", (lam(var(x)) app("run", [|f|], l)), (app("run", [|x|], l, v)), v)$,
  $"foreach" x "as" var(x) (.; f; g)$, $app("foreach", (lam(var(x)) app("run", [|f|], l)), (lam(var(x)) app("run", [|g|], l)), (app("run", [|x|], l, v)), v)$,
  $"def" x(x_1; ...; x_n) defas f defend g$, $(lam(x) app("run", [|g|], l, v)) (app(Y_(n+1), (lam(x, x_1, ..., x_n) [|f|])))$,
  $x(f_1; ...; f_n)$, $app("run", (app(x, [|f_1|], ..., [|f_n|])), l, v)$,
  $f update g$, $app("upd", [|f|], (app("run", [|g|], l)), l, v)$,
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss its different cases:

- "$.$": Returns its input value. This is the identity filter.
- $n$ or $s$: Returns the value corresponding to the number $n$ or string $s$.
- $var(x)$: Returns the value currently bound to the variable $var(x)$,
  by looking it up in the context.
  Wellformedness of the filter (as defined in @mir) ensures that such a value always exists.
- $[f]$: Creates an array from the output of $f$, using the operator defined in @values.
- ${}$: Creates an empty object.
- ${var(x): var(y)}$: Creates an object from the values bound to $var(x)$ and $var(y)$,
  using the operator defined in @values.
- $f, g$: Concatenates the outputs of $f$ and $g$.
- $f | g$: Composes $f$ and $g$, returning the outputs of $g$ applied to all outputs of $f$.
- $f alt g$: Returns $l$ if $l$ is not empty, else the outputs of $g$, where
  $l$ are the outputs of $f$ whose boolean values are not false.
- $f "as" var(x) | g$: For every output of $f$, binds it to the variable $var(x)$ and
  returns the output of $g$, where $g$ may reference $var(x)$.
  Unlike $f | g$, this runs $g$ with the original input value instead of an output of $f$.
  We can show that the evaluation of $f | g$ is equivalent to that of
  $f "as" var(x') | var(x') | g$, where $var(x')$ is a fresh variable.
  Therefore, we could be tempted to lower $f | g$ to
  $floor(f) "as" var(x') | var(x') | floor(g)$ in @tab:lowering.
  However, we cannot do this because we will see in @updates that
  this equivalence does _not_ hold for updates; that is,
  $(f | g) update sigma$ is _not_ equal to $(f "as" var(x') | var(x') | g) update sigma$.
- $var(x) cartesian var(y)$: Returns the output of a Cartesian operation "$cartesian$"
  (any of $eq.quest$, $eq.not$, $<$, $<=$, $>$, $>=$, $+$, $-$, $times$, $div$, and $mod$,
  as given in @tab:binops) on the values bound to $var(x)$ and $var(y)$.
  The semantics of the arithmetic operators are given in @arithmetic,
  the comparison operators are defined by the value order (see @value-ops),
  $l eq.quest r$ returns whether $l$ equals $r$, and
  $l eq.not r$ returns its negation.
- $"try" f "catch" g$: Replaces all outputs of $f$ that equal $"error"(e)$ for some $e$
  by the output of $g$ on the input $e$.
  At first sight, this seems to diverge from jq, which
  aborts the evaluation of $f$ after the first error.
  However, because lowering to MIR replaces
  $"try" f "catch" g$ with
  $"label" var(x') | "try" f "catch" (g, "break" var(x'))$ (see @tab:lowering),
  the overall behaviour described here corresponds to jq after all.
- $"label" var(x) | f$: Returns all values yielded by $f$ until $f$ yields
  an exception $"break"(var(x))$.
  This uses the function $"label"(l, var(x))$, which returns all elements of $l$ until
  the current element is an exception of the form $"break"(var(x))$:
  $ "label"(l, var(x)) := cases(
    stream(h) + "label"(t, var(x)) & "if" l = stream(h) + t "and" h != "break"(var(x)),
    stream() & "otherwise",
  ) $
  // TODO!
  To see that this is necessary, consider the example
  $ "def" f(x) defas ("label" var(x) | x), 0 defend "label" var(x) | f("break" var(x)). $
  With substitution, this is equivalent to
  $"label" var(x') | ("label" var(x'') | "break" var(x')), 0$
  and yields $stream(0)$, whereas
  without substitution, this would be equivalent to
  $"label" var(x) | ("label" var(x) | "break" var(x)), 0$
  and would yield $stream()$.#footnote[
    Would renaming all labels during lowering make the substitution step obsolete?
    Alas, no, because filter execution may generate an arbitrary number of labels.
    Consider the example $"def" f(x) defas "label" var(x) | f(x | "break" var(x)); f(.)$.
    This evaluates to
    $"label" var(x_1) | ... | "label" var(x_n) | f(. |
     "break" var(x_1) | ... | "break" var(x_n))$
    after $n$ evaluations of $f$, involving $n$ different labels.
  ]
- $"break" var(x)$: Returns a value $"break"(var(x))$.
  Similarly to the evaluation of variables $var(x)$ described above,
  wellformedness of the filter (as defined in @hir) ensures that
  the returned value $"break"(var(x))$ will be
  eventually handled by a corresponding filter
  $"label" var(x) | f$.
  That means that the evaluation of a wellformed filter can only yield
  values and errors, but never $"break"(var(x))$.
- $"if" var(x) "then" f "else" g$: Returns the output of $f$ if $var(x)$ is bound to either null or false, else returns the output of $g$.
- $.[p]$: Accesses parts of the input value;
  see @value-ops for the definitions of the operators.
  We apply $c$ to the path indices (which are variables)
  to replace them by their corresponding values.
- $fold x "as" var(x) (.; f)$: Folds $f$ over the values returned by $x$,
  starting with the current input as accumulator.
  The current accumulator value is provided to $f$ as input value and
  $f$ can access the current value of $x$ by $var(x)$.
  If $fold = "reduce" $, this returns only the final        values of the accumulator, whereas
  if $fold = "foreach"$, this returns also the intermediate values of the accumulator.
  We will define the functions
  $"reduce" ^c_v (l, var(x), f)$ and
  $"foreach"^c_v (l, var(x), f)$ in @folding.
- $x(f_1; ...; f_n)$: Calls an $n$-ary filter $x$.
  This also handles the case of calling nullary filters such as $"empty"$.
- $f update g$: Updates the input at positions returned by $f$ by $g$.
  We will discuss this in @updates.

An implementation may also define custom semantics for named filters.
For example, an implementation may define
$"error"|^c_v := "error"(v)$ and
$"keys"|^c_v := "keys"(v)$, see @simple-fns.
In the case of $"keys"$, for example, there is no obvious way to implement it by definition,
in particular because there is no simple way to obtain the domain of an object ${...}$
using only the filters for which we gave semantics in @tab:eval-semantics.
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
$ "fold" := lam(f, g, n) app(Y_2, (lam(F, l, v) app(l, (lam(h, t) app(f, h, v) bind (lam(y) app(g, h, y) + app(F, t, y))), (app(n, v))))) $
This function takes
two functions $f$ and $g$ that both take two values --- a list element and an accumulator --- and return a stream of value results, and
a function $n$ (for the nil case) from a value $x$ to a stream of value results.
From that, it creates a recursive function that
takes a stream of value results $l$ and an accumulator value $v$ and
returns a stream of value results.
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

/*
// TODO: this actually returns [1, 3] in jq 1.7
One of these problems is that if $g$ returns no output,
the collected paths may point to values that do not exist any more.

#example[
  Consider the input value $[1, 2, 2, 3]$ and the filter
  // '.[] |= (if . == 2 then empty else . end)'
  "$.[] update g$", where $g$ is "$"if" . eq.quest 2 "then" "empty"() "else" .$",
  which we might suppose to delete all values equal to 2 from the input list.
  However, the output of jq is $[1, 2, 3]$.
  What happens here is perhaps unexpected,
  but consistent with the above explanation of jq's semantics:
  jq builds the paths $.[0]$, $.[1]$, $.[2]$, and $.[3]$.
  Next, it applies $g$ to all paths.
  Applying $g$ to $.[1]$ removes the first occurrence of the number 2 from the list,
  leaving the list $[1, 2, 3]$ and the paths $.[2]$, $.[3]$ to update.
  However, $.[2]$ now refers to the number 3, and $.[3]$ points beyond the list.
] <ex:update>
*/

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
  $mu$, $mu update sigma$,
  $"empty"()$, $.$,
  $.$, $sigma$,
  $f | g$, $f update (g update sigma)$,
  $f, g$, $(f update sigma) | (g update sigma)$,
  $"if" var(x) "then" f "else" g$, $"if" var(x) "then" f update sigma "else" g update sigma$,
  $f alt g$, $"if" "first"(f alt "null") "then" f update sigma "else" g update sigma$,
)) <tab:update-props>

@tab:update-props gives a few properties that we want to hold for updates $mu update sigma$.
Let us discuss these for the different filters $mu$:
- $"empty"()$: Returns the input unchanged.
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
  See @folding for the definition of $"first"$.

While @tab:update-props allows us to define the behaviour of several filters
by reducing them to more primitive filters,
there are several filters $mu$ which cannot be defined this way.
We will therefore give the actual update semantics of $mu update sigma$ in @new-semantics
by defining $(mu update sigma)|^c_v$, not
by translating $mu update sigma$ to equivalent filters.

== Limiting interactions <limiting-interactions>

To define $(mu update sigma)|^c_v$, we first have to understand
how to prevent unwanted interactions between $mu$ and $sigma$.
In particular, we have to look at variable bindings/* and error catching*/.

//=== Variable bindings <var-bindings>

We can bind variables in $mu$; that is, $mu$ can have the shape $f "as" var(x) | g$.
Here, the intent is that $g$ has access to $var(x)$, whereas $sigma$ does not!
This is to ensure compatibility with jq's original semantics,
which execute $mu$ and $sigma$ independently,
so $sigma$ should not be able to access variables bound in $mu$.

#example[
  Consider the filter $0 "as" var(x) | mu update sigma$, where
  $mu$ is $(1 "as" var(x) | .[var(x)])$ and $sigma$ is $var(x)$.
  This updates the input array at index $1$.
  If $sigma$ had access to variables bound in $mu$,
  then the array element would be replaced by $1$,
  because the variable binding $0 "as" var(x)$ would be shadowed by $1 "as" var(x)$.
  However, in jq, $sigma$ does not have access to variables bound in $mu$, so
  the array element is replaced by $0$, which is the value originally bound to $var(x)$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.
]

We take the following approach to prevent variables bound in $mu$ to "leak" into $sigma$:
When evaluating $(mu update sigma)|^c_v$, we want
$sigma$ to always be executed with the same $c$.
That is, evaluating $(mu update sigma)|^c_v$ should never
evaluate $sigma$ with any context other than $c$.
In order to ensure that, we will define
$(mu update sigma)|^c_v$ not for a _filter_ $sigma$,
but for a _function_ $sigma(x)$, where
$sigma(x)$ returns the output of the filter $sigma|^c_x$.
This allows us to extend the context $c$ with bindings on the left-hand side of the update,
while executing the update filter $sigma$ always with the same original context $c$.

/*
=== Error catching <error-catching>

We can catch errors in $mu$; that is, $mu$ can have the shape $"try" f "catch" g$.
However, this should catch only errors that occur in $mu$,
_not_ errors that are returned by $sigma$.

#example[
  Consider the filter $mu update sigma$, where $mu$ is $.[]?$ and $sigma$ is $.+1$.
  The filter $mu$ is lowered to the MIR filter $"try" .[] "catch" "empty"()$.
  The intention of $mu update sigma$ is to
  update all elements $.[]$ of the input value, and if $.[]$ returns an error
  (which occurs when the input is neither an array nor an object, see @accessing),
  to just return the input value unchanged.
  When we run $mu update sigma$ with the input $0$,
  the filter $.[]$ fails with an error, but
  because the error is caught immediately afterwards,
  $mu update sigma$ consequently just returns the original input value $0$.
  The interesting part is what happens when $sigma$ throws an error:
  This occurs for example when running the filter with the input $[{}]$.
  This would run $. + 1$ with the input ${}$, which yields an error (see @arithmetic).
  This error _is_ returned by $mu update sigma$.
]

This raises the question:
How can we execute $("try" f "catch" g) update sigma$ and distinguish
errors stemming from $f$ from errors stemming from $sigma$?

We came up with the solution of _polarised exceptions_.
In a nutshell, we want every exception that is returned by $sigma$ to be
marked in a special way such that it can be ignored by a try-catch in $mu$.
For this, we assume the existence of two functions
$"polarise"(x)$ and $"depolarise"(x)$ from a value result $x$ to a value result.
If $x$ is an exception, then
$"polarise"(x)$ should return a polarised version of it, whereas
$"depolarise"(x)$ should return an unpolarised version of it, i.e. it should
remove any polarisation from an exception.
Every exception created by $"error"(e)$ is unpolarised.
With this method, when we evaluate an expression $"try" f "catch" g$ in $mu$,
we can analyse the output of $f update sigma$, and only catch _unpolarised_ errors.
That way, errors stemming from $mu$ are propagated,
whereas errors stemming from $f$ are caught.
*/


== New semantics <new-semantics>

We will now give semantics that define the output of
$(f update g)|^c_v$ as referred to in @semantics.

We will first combine the techniques in @limiting-interactions to define
$(f update g)|^c_v$ for two _filters_ $f$ and $g$ by
$(f update sigma)|^c_v$, where
$sigma$ now is a _function_ from a value to a stream of value results:
$ (f update g)|^c_v := (f update sigma)|^c_v", where"
sigma(x) = g|^c_x. $
We use a function instead of a filter on the right-hand side to
limit the scope of variable bindings as explained in @limiting-interactions/*, and
we use $"polarise"$ to
restrict the scope of caught exceptions, as discussed in @error-catching.
Note that we $"depolarise"$ the final outputs of $f update g$ in order to
prevent leaking polarisation information outside the update*/.

#figure(caption: [Update semantics. Here, $mu$ is a filter and $sigma(v)$ is a function from a value $v$ to a stream of value results.], table(columns: 2,
  $phi$, $app("upd", [|phi|], sigma, l, v)$,
  $.$, $app(sigma, v)$,
  $f | g$, $app("upd", [|f|], (app("upd", [|g|], sigma, l)), l, v)$,
  $f, g$, $app("upd", [|f|], sigma, l, v) bind app("upd", [|g|], sigma, l)$,
  $f alt g$, $app("upd", (app((app("run", [|f|], l, v) bind "trues"), (lam(\_, \_) [|f|]), [|g|])), l, v)$,
  $.[p]^?$, $stream(v[c(p)]^? update sigma)$,
  $f "as" var(x) | g$, $app("reduce", (lam(var(x)) app("upd", [|g|], sigma, l)), (app("run", [|f|], l, v)), v)$,
  $"if" var(x) "then" f "else" g$, $app("upd", (app((app("bool", var(x))), [|f|], [|g|])), sigma, l, v)$,
  $"break" var(x)$, $stream(app("break", var(x)))$,
  // TODO!
  $fold x "as" var(x) (.; f)$, $fold^c_v (x|^c_v, var(x), f, sigma)$,
  $"reduce" x "as" var(x) (.; f)$, $app("reduce"_models, (lam(sigma, var(x)) app("upd", [|f|], sigma, l)), (app("run", [|x|], l, v)), v)$,
  $"foreach" x "as" var(x) (.; f; g)$, $app("foreach"_models, (lam(sigma, var(x)) app("upd", [|f|], sigma, l)), (lam(var(x)) app("upd", [|g|], sigma, l)), (app("run", [|x|], l, v)), v)$,
  $"def" x(x_1; ...; x_n) defas f defend g$, $(lam(x) app("upd", [|g|], sigma, l, v)) (app(Y_(n+1), (lam(x, x_1, ..., x_n) [|f|])))$,
  $x(f_1; ...; f_n)$, $app("upd", (app(x, [|f_1|], ..., [|f_n|])), sigma, l, v)$,
)) <tab:update-semantics>

@tab:update-semantics shows the definition of $(mu update sigma)|^c_v$.
Several of the cases for $mu$, like
"$.$", "$f | g$", "$f, g$", and "$"if" var(x) "then" f "else" g$"
are simply relatively straightforward consequences of the properties in @tab:update-props.
We discuss the remaining cases for $mu$:
- $f alt g$: Updates using $f$ if $f$ yields some non-false value, else updates using $g$.
  Here, $f$ is called as a "probe" first.
  If it yields at least one output that is considered "true"
  (see @semantics for the definition of $"trues"$),
  then we update at $f$, else at $g$.
  This filter is unusual because is the only kind where a subexpression is both
  updated with ($(f update sigma)|^c_v$) and evaluated ($f|^c_v$).
- $.[p]^?$: Applies $sigma$ to the current value at the path part $p$
  using the update operators in @value-ops.
- $f "as" var(x) | g$:
  Folds over all outputs of $f$, using the input value $v$ as initial accumulator and
  updating the accumulator by $g update sigma$, where
  $var(x)$ is bound to the current output of $f$.
  The definition of $"reduce"$ is given in @folding.
/*
- $"try" f "catch" g$: Returns the output of $f update sigma$,
  mapping errors occurring in $f$ to $g$. The definition of the function $"catch"$ is
  $ "catch"(x, g, c, v) := cases(
    sum_(y in g|^c_(e)) stream("error"(y)) & "if" x = "error"(e)", " x "is unpolarised, and" g|^c_x != stream(),
    stream(v) & "if" x = "error"(e)", " x "is unpolarised, and" g|^c_x = stream(),
    stream(x) & "otherwise"
) $
  The function $"catch"(x, g, c, v)$ analyses $x$ (the current output of $f$):
  If $x$ is no unpolarised error, $x$ is returned.
  For example, that is the case if the original right-hand side of the update
  returns an error, in which case we do not want this error to be caught here.
  However, if $x$ is an unpolarised error, that is,
  an error that was caused on the left-hand side of the update,
  it has to be caught here.
  In that case, $"catch"$ analyses the output of $g$ with input $x$:
  If $g$ yields no output, then it returns the original input value $v$,
  and if $g$ yields output, all its output is mapped to errors!
  This behaviour might seem peculiar,
  but it makes sense when we consider the jq way of implementing updates via paths:
  When evaluating some update $mu update sigma$ with an input value $v$,
  the filter $mu$ may only return paths to data contained within $v$.
  When $mu$ is $"try" f "catch" g$,
  the filter $g$ only receives inputs that stem from errors,
  and because $v$ cannot contain errors, these inputs cannot be contained in $v$.
  Consequentially, $g$ can never return any path pointing to $v$.
  The only way, therefore, to get out alive from a $"catch"$ is for $g$ to return ... nothing.
- $"break"(var(x))$: Breaks out from the update.#footnote[
    Note that unlike in @semantics, we do not define the update semantics of
    $"label" var(x) | f$, which could be used to resume an update after a $"break"$.
    The reason for this is that this requires
    an additional type of $"break"$ exceptions that
    carries the current value alongside the variable, as well as
    variants of the value update operators in @updating that can handle unpolarised breaks.
    Because making update operators handle unpolarised breaks
    renders them considerably more complex and
    we estimate that label expressions are
    rarely used in the left-hand side of updates anyway,
    we think it more beneficial for the presentation to forgo label expressions here.
  ]
*/
- $fold x "as" var(x) (.; f)$: Folds $f$ over the values returned by $var(x)$.
  We will discuss this in @folding-update.
- $x(f_1; ...; f_n)$, $x$: Calls filters.
  This is defined analogously to @tab:eval-semantics.

There are many filters $mu$ for which
$(mu update sigma)|^c_v$ is not defined,
for example $var(x)$, $[f]$, and ${}$.
In such cases, we assume that $(mu update sigma)|^c_v$ returns an error just like jq,
because these filters do not return paths to their input data.
Our semantics support all kinds of filters $mu$ that are supported by jq, except for
$"label" var(x) | g$ and $"try" f "catch" g$.

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
  $"error"([])$.
  That is because $.[]$ does not yield any value for the input,
  so $"error" update 1$ is executed, which yields an error.
]


== Folding <folding-update>

// TODO: update this for `foreach/3` and remove `for`

In @folding, we have seen how to evaluate folding filters of the shape
$fold x "as" var(x) (.; f)$, where $fold$ is either $"reduce"$ or $"foreach"$.
Here, we will define update semantics for these filters.
These update operations are _not_ supported in jq 1.7; however,
we will show that they arise quite naturally from previous definitions.

Let us start with an example to understand folding on the left-hand side of an update.

#example[
  Let $v = [[[2], 1], 0]$ be our input value
  and $mu$ be the filter $fold (0, 0) "as" var(x) (.; .[var(x)])$.
  The regular evaluation of $mu$ with the input value as described in @semantics yields
  $ mu|^{}_v = cases(
    stream(#hide($[[2], 1], $) [2]) & "if" fold = "reduce",
    stream(       [[2], 1],    [2]) & "if" fold = "foreach",
  ) $
  When $fold = "foreach"$, the paths corresponding to the output are $.[0]$ and $.[0][0]$, and
  when $fold = "reduce"$, the paths are just $.[0][0]$.
  Given that all outputs have corresponding paths, we can update over them.
  For example, taking $. + [3]$ as filter $sigma$, we should obtain the output
  #let h3 = hide($, 3$)
  $ (mu update sigma)^{}_v = cases(
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
  $ mu update sigma = cases(
    .[0] update #hs      .[0] update sigma   & "if" fold = "reduce",
    .[0] update sigma | (.[0] update sigma)  & "if" fold = "foreach",
  ) $
]

We will now formally define the functions used in @tab:update-semantics.
For this, we first introduce a function $"fold"^c_v (l, var(x), f, g, sigma, o)$,
which resembles its corresponding function in @folding,
but which adds an argument for the update filter $sigma$:

$ "fold"_update := lam(f, g, n) app(Y_2, (lam(F, l, v) app(l, (lam(h, t) app(f, (lam(x) app(g, h, x) bind app(F, t)), h, v)), (app(n, v))))) $

/*
$ "fold"^c_v (l, var(x), f, g, sigma, o) := cases(
  (f update sigma')|^(c{var(x) |-> h})_v & "if" l = stream(h) + t,
  o(v) & "otherwise" (l = stream()),
) $
where
$ sigma'(x) = sum_(y in (g update sigma)|^(c{var(x) |-> h})_x) "fold"^c_y (t, var(x), f, g, sigma, o). $
*/

Using this function, we can now define

$  "reduce"_models &:= lam(f   &&) app("fold", f, (lam(h, v) stream(v)), && sigma) \
  "foreach"_models &:= lam(f, g&&) app("fold", f, g, && (lam(v) stream(ok(v)))) $
