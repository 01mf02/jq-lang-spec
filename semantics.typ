#import "common.typ": *

= Evaluation Semantics <semantics>

In this section, we will define a function $phi|^c_v$ that returns
the output of the filter $phi$ in the context $c$ on the input value $v$.

Let us start with a few definitions.
A _context_ $c$ is a mapping
from variables $var(x)$ to values and
from identifier-arity pairs $(x, n)$ to triples $(a, f, c)$, where
$a$ is an identifier sequence with length $n$,
$f$ is a filter, and
$c$ is a context.
Contexts store what variables and filters are bound to.

We are now going to introduce a few helper functions.
The first function helps define filters such as if-then-else and alternation ($f alt g$):
$ "ite"(v, i, t, e) = cases(
  t & "if" v = i,
  e & "otherwise"
) $

Next, we define a function that is used to define alternation.
$"trues"(l)$ returns those elements of $l$ whose boolean values are not false.
Note that in our context, "not false" is _not_ the same as "true", because
the former includes exceptions, whereas the latter excludes them,
and $"bool"(x)$ _can_ return exceptions, in particular if $x$ is an exception.

$ "trues"(l) := sum_(x in l, "bool"(x) != "false") stream(x) $

#figure(caption: "Evaluation semantics.", table(columns: 2,
  $phi$, $phi|^c_v$,
  $.$, $stream(v)$,
  $n "or" s$, $stream(phi)$,
  $var(x)$, $stream(c(var(x)))$,
  $[f]$, $stream([f|^c_v])$,
  ${}$, $stream({})$,
  ${var(x): var(y)}$, $stream({c(var(x)): c(var(y))})$,
  $f, g$, $f|^c_v + g|^c_v$,
  $f | g$, $sum_(x in f|^c_v) g|^c_x$,
  $f alt g$, $"ite"("trues"(f|^c_v), stream(), g|^c_v, "trues"(f|^c_v))$,
  $f "as" var(x) | g$, $sum_(x in f|^c_v) g|^(c{var(x) |-> x})_v$,
  $var(x) cartesian var(y)$, $stream(c(var(x)) cartesian c(var(y)))$,
  $"try" f "catch" g$, $sum_(x in f|^c_v) cases(
    g|^c_e & "if" x = "error"(e),
    stream(x) & "otherwise"
  )$,
  $"label" var(x) | f$, $"label"(f|^c_v, var(x))$,
  $"break" var(x)$, $stream("break"(var(x)))$,
  $var(x) "and" f$, $"junction"(c(var(x)), "false", f|^c_v)$,
  $var(x) "or"  f$, $"junction"(c(var(x)), "true" , f|^c_v)$,
  $"if" var(x) "then" f "else" g$, $"ite"("bool"(c(var(x))), "true", f|^c_v, g|^c_v)$,
  $.[p]^?$, $v[c(p)]^?$,
  /*
  $.[]$, $v[]$,
  $.[var(x)]$, $stream(v[c(var(x))])$,
  $.[var(x):var(y)]$, $stream(v[c(var(x)):c(var(y))])$,
  */
  $fold x "as" var(x) (.; f)$, $fold^c_v (x|^c_v, var(x), f)$,
  $"def" x(x_1; ...; x_n) defas f defend g$, $g|^(c union {(x, n) |-> ([x_1, ..., x_n], f, c)})_v$,
  $x(f_1; ...; f_n)$, $f|^(c' union union.big_i {x_i |-> (f_i, c)})_v "if" c((x, n)) = ([x_1, ..., x_n], f, c')$,
  $f update g$, [see @updates]
)) <tab:eval-semantics>

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss its different cases:

- "$.$": Returns its input value. This is the identity filter.
- $n$ or $s$: Returns the value corresponding to the number $n$ or string $s$.
- $var(x)$: Returns the value currently bound to the variable $var(x)$,
  by looking it up in the context.
  Wellformedness of the filter (as defined in @hir) ensures that such a value always exists.
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
  Note that this diverges from jq, which aborts the evaluation of $f$ after the first error.
  This behaviour can be simulated in our semantics, by replacing
  $"try" f "catch" g$ with
  $"label" var(x') | "try" f "catch" (g, "break" var(x'))$.
- $"label" var(x) | f$: Returns all values yielded by $f$ until $f$ yields
  an exception $"break"(var(x))$.
  This uses the function $"label"(l, var(x))$, which returns all elements of $l$ until
  the current element is an exception of the form $"break"(var(x))$:
  $ "label"(l, var(x)) := cases(
    stream(h) + "label"(t, var(x)) & "if" l = stream(h) + t "and" h != "break"(var(x)),
    stream() & "otherwise",
  ) $
- $"break" var(x)$: Returns a value $"break"(var(x))$.
  Similarly to the evaluation of variables $var(x)$ described above,
  wellformedness of the filter (as defined in @hir) ensures that
  the returned value $"break"(var(x))$ will be
  eventually handled by a corresponding filter
  $"label" var(x) | f$.
  That means that the evaluation of a wellformed filter can only yield
  values and errors, but never $"break"(var(x))$.
- $var(x) "and" f$: Returns false if $var(x)$ is bound to either null or false, else
  returns the output of $f$ mapped to boolean values.
  This uses the function $"junction"(x, v, l)$, which returns
  just $v$ if the boolean value of $x$ is $v$ (where $v$ will be true or false),
  otherwise the boolean values of the values in $l$.
  Here, $"bool"(v)$ returns the boolean value as given in @simple-fns.
  $ "junction"(x, v, l) := "ite"lr(("bool"(x), v, stream(v), sum_(y in l) stream("bool"(y))), size: #50%) $
- $var(x) "or" f$: Similar to its "and" counterpart above.
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
// TODO!
- $x(f_1; ...; f_n)$: Calls an $n$-ary filter $x$ that is defined by $x(x_1; ...; x_n) := f$.
  The output is that of the filter $f$, where
  each filter argument $x_i$ is bound to $(f_i, c)$.
  This also handles the case of calling nullary filters such as $"empty"$.
- $x$: Calls a filter argument.
  By the well-formedness requirements given in @hir,
  this must occur within the right-hand side of a definition whose arguments include $x$.
  This requirement also ensures that $x in "dom"(c)$,
  because an $x$ can only be evaluated as part of a call to the filter where it was bound, and
  by the semantics of filter calls above, this adds a binding for $x$ to the context.
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

In this subsection, we will define the functions $fold^c_v (l, var(x), f)$
(where $fold$ is either $"foreach"$ or $"reduce"$),
which underlie the semantics for the folding operators
$fold x "as" var(x) (.; f)$.

Let us start by defining a general folding function $"fold"^c_v (l, var(x), f, o)$: It takes
a stream of value results $l$,
a variable $var(x)$,
a filter $f$, and
a function $o(x)$ from a value $x$ to a stream of values.
This function folds over the elements in $l$, starting from the accumulator value $v$.
It yields the next accumulator value(s) by evaluating $f$
with the current accumulator value as input and
with the variable $var(x)$ bound to the first element in $l$.
If $l$ is empty, then
$v$ is called a  _final_        accumulator value and is returned, otherwise
$v$ is called an _intermediate_ accumulator value and $o(v)$ is returned.

$ "fold"^c_v (l, var(x), f, o) := cases(
  o(v) + sum_(x in f|^(c{var(x) |-> h})_v) "fold"^c_x (t, var(x), f, o) & "if" l = stream(h) + t,
  stream(        v ) & "otherwise" (l = stream())
) $

We use two different functions for $o(v)$;
the first returns nothing,  corresponding to $"reduce" $ which does not return intermediate values, and
the other returns just $v$, corresponding to $"foreach"$ which returns intermediate values.
Instantiating $"fold"$ with these two functions, we obtain the following:

$ "reduce"^c_v (l, var(x), f) :=& "fold"^c_v (l, var(x), f, o) "where" o(v) = stream(#hide[v]) \
     "for"^c_v (l, var(x), f) :=& "fold"^c_v (l, var(x), f, o) "where" o(v) = stream(v)
$

Here, $"reduce"^c_v (l, var(x), f)$ is the function that is used in @tab:eval-semantics.
However, $"for"^c_v (l, var(x), f)$ does _not_ implement the semantics of $"foreach"$,
because it yields the initial accumulator value, whereas $"foreach"$ omits it.

#example[
  If we would set $"foreach"^c_v (l, var(x), f) := "for"^c_v (l, var(x), f)$, then evaluating
  $"foreach" (1, 2, 3) "as" var(x) (0; . + var(x))$ would yield
  $stream(0, 1, 3, 6)$, but jq evaluates it to
  $stream(   1, 3, 6)$.
]

For that reason, we define $"foreach"$ in terms of $"for"$,
but with a special treatment for the initial accumulator:

$ "foreach"^c_v (l, var(x), f) := cases(
  sum_(x in f|^(c{var(x) |-> h})_v) "for"^c_x (t, var(x), f) & "if" l = stream(h) + t,
  stream() & "otherwise",
) $

We will now look at what the evaluation of the various folding filters expands to.
Apart from $"reduce"$ and $"foreach"$, we will also consider a hypothetical filter
$"for" x "as" var(x) (.; f)$ that is defined by the function
$"for"^c_v (l, var(x), f)$, analogously to the other folding filters.

Assuming that the filter $x$ evaluates to $stream(x_0, ..., x_n)$,
then $"reduce"$ and $"for"$ expand to

$ "reduce"   x "as" var(x) (.; f) =&     x_0 "as" var(x) | f & wide
  "for"      x "as" var(x) (.; f) =& ., (x_0 "as" var(x) | f \
|& ... &
|& ... \
|&     x_n "as" var(x) | f &
|& ., (x_n "as" var(x) | f)...)
$
and $"foreach"$ expands to
$ "foreach" x "as" var(x) (.; f)
=& #hide($., ($) x_0 "as" var(x) | f \
|& ., (x_1 "as" var(x) | f \
|& ... \
|& ., (x_n "as" var(x) | f)...).
$

We can see that the special treatment of the initial accumulator value also shows up
in the expansion of $"foreach"$.
In contrast, the hypothetical $"for"$ filter looks more symmetrical to $"reduce"$.

Note that jq implements only a restricted version of these folding operators
that discards all output values of $f$ after the first output.
That means that in jq,
$fold x "as" var(x) (.;         f )$ is equivalent to
$fold x "as" var(x) (.; "first"(f))$.
Here, we assume the definition $"first"(f) := "label" var(x) | f | (., "break" var(x))$.
This returns the first output of $f$ if $f$ yields any output, else nothing.



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
  $mu$, $(mu update sigma)|^c_v$,
  $.$, $sigma(v)$,
  $f | g$, $(f update sigma')|^c_v "where" sigma'(x) = (g update sigma)|^c_x$,
  $f, g$, $sum_(x in (f update sigma)|^c_v) (g update sigma)|^c_x$,
  $f alt g$, $"ite"("trues"(f|^c_v), stream(), (g update sigma)|^c_v, (f update sigma)|^c_v)$,
  $.[p]^?$, $stream(v[c(p)]^? update sigma)$,
  $f "as" var(x) | g$, $"reduce"^c_v (f|^c_v, var(x), (g update sigma))$,
  $"if" var(x) "then" f "else" g$, $"ite"(c(var(x)), "true", (f update sigma)|^c_v, (g update sigma)|^c_v)$,
//$"try" f "catch" g$, $sum_(x in (f update sigma)|^c_v) "catch"(x, g, c, v)$,
  $"break" var(x)$, $stream("break"(var(x)))$,
  $fold x "as" var(x) (.; f)$, $fold^c_v (x|^c_v, var(x), f, sigma)$,
  $x(f_1; ...; f_n)$, $(f update sigma)|^(c union union.big_i {x_i |-> (f_i, c)})_v "if" x(x_1; ...; x_n) := f$,
  $x$, $(f update sigma)|^c'_v "if" c(x) = (f, c')$,
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
    stream(#hide($v, [[2], 1], $) [2]) & "if" fold = "reduce",
    stream(       v, [[2], 1],    [2]) & "if" fold = "for",
    stream(#hide($v, $) [[2], 1], [2]) & "if" fold = "foreach",
  ) $
  When $fold = "for"$, the paths corresponding to the output are $.$, $.[0]$, and $.[0][0]$, and
  when $fold = "reduce"$, the paths are just $.[0][0]$.
  Given that all outputs have corresponding paths, we can update over them.
  For example, taking $. + [3]$ as filter $sigma$, we should obtain the output
  #let h3 = hide($, 3$)
  $ (mu update sigma)^{}_v = cases(
    stream([[[2, 3], 1#h3], 0#h3]) & "if" fold = "reduce",
    stream([[[2, 3], 1, 3], 0, 3]) & "if" fold = "for",
    stream([[[2, 3], 1, 3], 0#h3]) & "if" fold = "foreach",
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
$fold x "as" var(x) (.; f) update sigma$,
substitute the left-hand side by the defining equations in @folding and
expand everything using the properties in @update-props.
This yields
$ "reduce"   x "as" var(x) (.; f) update sigma =&         ((x_0 "as" var(x) | f) & wide
  "for"      x "as" var(x) (.; f) update sigma =& sigma | ((x_0 "as" var(x) | f) \
update& ... &
update& ... \
update&         ((x_n "as" var(x) | f) &
update& sigma | ((x_n "as" var(x) | f) \
update& sigma)...) &
update& sigma)...)
$
and $"foreach"$ steps out of line again by not applying $sigma$ initially:
$ "foreach" x "as" var(x) (.; f) update sigma
=& #hide($sigma |$) ((x_0 "as" var(x) | f) \
update& sigma | ((x_1 "as" var(x) | f) \
update& ... \
update& sigma | ((x_n "as" var(x) | f) \
update& sigma)...).
$

#example[
  To see the effect of above equations, let us reconsider
  the input value and the filters from @ex:folding-update.
  Using some liberty to write $.[0]$ instead of $0 "as" var(x) | .[var(x)]$, we have:
  #let hs = hide($sigma | ($)
  $ mu update sigma = cases(
    #hs      .[0] update #hs      .[0] update sigma   & "if" fold = "reduce",
    sigma | (.[0] update sigma | (.[0] update sigma)) & "if" fold = "for",
    #hs      .[0] update sigma | (.[0] update sigma)  & "if" fold = "foreach",
  ) $
]

We will now formally define the functions
$fold^c_v (l, var(x), f, sigma)$ used in @tab:update-semantics.
For this, we first introduce a function $"fold"^c_v (l, var(x), f, sigma, o)$,
which resembles its corresponding function in @folding,
but which adds an argument for the update filter $sigma$:

$ "fold"^c_v (l, var(x), f, sigma, o) := cases(
  sum_(y in o(v)) (f update sigma')|^(c{var(x) |-> h})_y & "if" l = stream(h) + t "and" sigma'(x) = "fold"^c_x (t, var(x), f, sigma, o),
  sigma(v) & "otherwise" (l = stream())
) $

Using this function, we can now define

$ "reduce"^c_v (l, var(x), f, sigma) :=& "fold"^c_v (l, var(x), f, sigma, o) "where" o(v) = #hide($sigma$)stream(v) \
     "for"^c_v (l, var(x), f, sigma) :=& "fold"^c_v (l, var(x), f, sigma, o) "where" o(v) =  sigma(v)
$
as well as
$ "foreach"^c_v (l, var(x), f, sigma) := cases(
  (f update sigma')|^(c{var(x) |-> h})_v & "if" l = stream(h) + t "and" sigma'(x) = "for"^c_x (t, var(x), f, sigma),
  stream(v) & "otherwise",
) $

