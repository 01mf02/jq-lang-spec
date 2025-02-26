#import "common.typ": *

= Values <values>

In this section, we define several data types, such as
values, value results, and streams, in simply typed lambda calculus.
To ease the understanding, we will informally give type names to certain terms.

While jq operates uniquely on JSON values,
we define the jq semantics for a general value type $cal(V)$.
This value type must satisfy several properties that will be given in @value-ops.
Furthermore, we assume that $cal(V)$ can be encoded in lambda calculus.

We encode boolean values as follows:
$  "true": bb(B) := lam(t, f) t \
  "false": bb(B) := lam(t, f) f $

We assume the existence of functions
$"succ": bb(N) -> bb(N)$ and
$"zero": bb(N)$ to construct natural numbers, as well as a function
$"nat_eq": bb(N) -> bb(N) -> bb(B)$ that returns
$"true"$ if two natural numbers are equal, else $"false"$.
We use natural numbers to store label identifiers.

The elements returned by our filters are _value results_ $cal(R)$, which are
either OK or an exception (an error or a break).

$ "ok"   &: cal(V) -> cal(R) := lam(x, o, e, b) app(o, x) \
  "err"  &: cal(V) -> cal(R) := lam(x, o, e, b) app(e, x) \
  "break"&:  bb(N) -> cal(R) := lam(x, o, e, b) app(b, x) $

We will use _streams_ $cal(S)$ of value results as return type of filters.

$ "cons"&: cal(R) -> cal(S) -> &&cal(S) := lam(h, t) && lam(c, n) app(c, h, t) \
   "nil"&:                     &&cal(S) :=           && lam(c, n) n $

We write a stream
$"nil"$ as $stream()$ and
$app("cons", r_1, (app("cons", r_2, ...)))$ as $stream(r_1, r_2, ...)$.

We assume the existence of a set of Y combinators $Y_n$ that we will use to
define recursive functions of arity $n$.
For each $n$, we have that $Y_n f = f (Y_n f)$ holds.
Furthermore, the types of $Y_n$ are:

$ Y_1:& ((T_1 &&-> U) -> T_1 &&-> U) -> T_1 &&-> U \
  ... \
  Y_n:& ((T_1 -> ... -> T_n &&-> U) -> T_1 -> ... -> T_n &&-> U) -> T_1 -> ... -> T_n &&-> U $

We define the concatenation of two streams $l$ and $r$ as
$ l + r := app(Y_1, (lam(f, l) app(l, (lam(h, t) app("cons", h, (app(f, t)))), r)), l), $
which satisfies the equational property
$ l + r = app(l, (lam(h, t) app("cons", h, (t + r))), r). $
For simplicity, we will define recursive functions from here on mostly by equational properties,
from which we could easily derive proper definitions using the $Y_n$ combinators.

We define three monadic bind operators to describe composition.
For a result $r$ and a function $f$ from a value to a result,
$s bindr f$ applies $f$ to $r$ if it is OK, else returns $r$ unchanged.
For a stream $s$ and a function $f$ from a _value result_ to a stream,
$s bindl f$ applies $f$ to all elements of $s$ and concatenates the outputs.
For a stream $s$ and a function $f$ from a _value_ to a stream,
$s bind f$ applies OK values in $s$ to $f$ and returns exception values in $s$.
$ &bindr&&: cal(R) &&-> (cal(V) &&-> &cal(R)&) &&-> cal(R) &&:= lam(r, f) app(r, (lam(o) app(f, o)), (lam(e) r), (lam(b) r)) \
  &bindl&&: cal(S) &&-> (cal(R) &&-> &cal(S)&) &&-> cal(S) &&:= lam(s, f) app(s, (lam(h, t) app(f, h) + (t bindl f)), "nil") \
  &bind &&: cal(S) &&-> (cal(V) &&-> &cal(S)&) &&-> cal(S) &&:= lam(s, f) s bindl (lam(x) app(x, (lam(o) app(f, o)), (lam(e) stream(x)), (lam(b) stream(x)))) $


/*
An _error_ can be constructed from a value by the function $"error"(v)$.
The $"error"$ function is bijective; that is,
if we have an error $e$, then there is a unique value $v$ with $e = "error"(v)$.
In the remainder of this text, we will write just "error"
to denote calling $"error"(v)$ with some value $v$.
This is done such that this specification does not need to fix
the precise error value that is returned when an operation fails.

An _exception_ either is an error or has the shape $"break"(var(x))$.
The latter will become relevant starting from @semantics.

A _value result_ is either a value or an exception.
*/

/*
Given some stream $l = stream(x_0, ..., x_n)$, we write
$sum_(x in l) f(x)$ to denote $f(x_0) + ... + f(x_n)$.
We use this frequently to map a function over a stream,
by having $f(x)$ return a stream itself.
*/

/*
In this text, we will see many functions that take values as arguments.
By convention, for any of these functions $f(v_1, ..., v_n)$,
we extend their domain to value results such that $f(v_1, ..., v_n)$ yields $v_i$
(or rather $stream(v_i)$ if $f$ returns streams)
if $v_i$ is an exception and for all $j < i$, $v_j$ is a value.
For example, in @arithmetic, we will define $l + r$ for values $l$ and $r$,
and by our convention, we extend the domain of addition to value results such that
if $l$ is an exception, then $l + r$ returns just $l$, and
if $l$ is a value, but $r$ is an exception, then $l + r$ returns just $r$.
*/

== Value operations <value-ops>

In this subsection, we specify the functions and operations
that a value type must implement.

For the value type $cal(V)$, there must be a type of numbers and a type of strings, such that
for any number $n$, $n$ is a value, and
for any string $s$, $s$ is a value.
Furthermore, for any boolean $b$, $b$ is a value.
By convention, we will write
$v$ for values,
$n$ for numbers, and
$s$ for strings
in the remainder of this text.

There is a total order $<=$ on values.
We say that $v_1 = v_2$ if and only if both $v_1 <= v_2$ and $v_2 <= v_1$.
For JSON values, this order is given in @json-order.

We assume the existence of several functions:

- $"arr"_0: cal(V)$ yields an empty array.
- $"arr"_1: cal(V) -> cal(V)$ constructs a singleton array from a value.
- $"obj"_0: cal(V)$ yields an empty object.
- $"obj"_1: cal(V) -> cal(V) -> cal(R)$ constructs a singleton object from a key and value.
  (It returns a value result instead of a value because it
  may fail in case that the provided key is not a string.)
- $"bool": cal(V) -> bb(B)$ takes a value and returns a boolean.

Let $p$ a path part (as defined in @syntax) containing values as indices.
We assume two operators:
- The _access operator_ $v[p]$ extracts values contained within $v$
  at positions given by $p$, yielding a stream of value results.
  This operator will be used in @semantics and
  is defined for JSON values in @json-access.
- The _update operator_ $v[p]^? update f$ replaces
  those elements $v' = v[p]$ in $v$ by
  the output of $app(f, v')$, where $f: cal(V) -> cal(S)$.
  The update operator yields a single value result.
  This operator will be used in @updates and
  is defined for JSON values in @json-update.

If $v[p]$ returns an error, then
$v[p]  update f$ should yield an error and
$v[p]? update f$ should yield $v$.
We define $v[p]? = v[p] bindl lam(r) app(r, (lam(o) stream(r)), (lam(e) stream()), (lam(b) stream(r)))$.
This simply discards any error yielded by $v[p]$.
