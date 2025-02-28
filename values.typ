#import "common.typ": *

= Values <values>

In this section, we define several data types, such as
values, value results, and lists, in simply typed lambda calculus.
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

We will use _lists_ $cal(L)$ of value results as return type of filters.
Because the jq language is evaluated lazily, lists can be infinite.

$ "cons"&: cal(R) -> cal(L) -> &&cal(L) := lam(h, t) && lam(c, n) app(c, h, t) \
   "nil"&:                     &&cal(L) :=           && lam(c, n) n $

We write the empty list
$"nil"$ as $stream()$ and
$app("cons", r_1, (app("cons", r_2, ...)))$ as $stream(r_1, r_2, ...)$.

We assume the existence of a set of Y combinators $Y_n$ that we will use to
define recursive functions of arity $n$.
For each $n$, we have that $Y_n f = f (Y_n f)$ holds.
Furthermore, the types of $Y_n$ are:

$ Y_1:& ((T_1 &&-> U) -> T_1 &&-> U) -> T_1 &&-> U \
  ... \
  Y_n:& ((T_1 -> ... -> T_n &&-> U) -> T_1 -> ... -> T_n &&-> U) -> T_1 -> ... -> T_n &&-> U $

We define the concatenation of two lists $l$ and $r$ as
$ l + r := app(Y_1, (lam(f, l) app(l, (lam(h, t) app("cons", h, (app(f, t)))), r)), l), $
which satisfies the equational property
$ l + r = app(l, (lam(h, t) app("cons", h, (t + r))), r). $
For simplicity, we will define recursive functions from here on mostly by equational properties,
from which we could easily derive proper definitions using the $Y_n$ combinators.

We define three monadic bind operators to describe composition.
For a result $r$ and a function $f$ from a value to a result,
$l bindr f$ applies $f$ to $r$ if it is OK, else returns $r$ unchanged.
For a list $l$ and a function $f$ from a _value result_ to a list,
$l bindl f$ applies $f$ to all elements of $l$ and concatenates the outputs.
For a list $l$ and a function $f$ from a _value_ to a list,
$l bind f$ applies OK values in $l$ to $f$ and returns exception values in $l$.
$ &bindr&&: cal(R) &&-> (cal(V) &&-> &cal(R)&) &&-> cal(R) &&:= lam(r, f) app(r, (lam(o) app(f, o)), (lam(e) r), (lam(b) r)) \
  &bindl&&: cal(L) &&-> (cal(R) &&-> &cal(L)&) &&-> cal(L) &&:= lam(l, f) app(l, (lam(h, t) app(f, h) + (t bindl f)), "nil") \
  &bind &&: cal(L) &&-> (cal(V) &&-> &cal(L)&) &&-> cal(L) &&:= lam(l, f) l bindl (lam(x) app(x, (lam(o) app(f, o)), (lam(e) stream(x)), (lam(b) stream(x)))) $


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
Their concrete definitions for JSON values are given in @json.

For the value type $cal(V)$, there must be a type of numbers and a type of strings, such that
for any number $n$, $n$ is a value, and
for any string $s$, $s$ is a value.
Furthermore, for any boolean $b$, $b$ is a value.
By convention, we will write
$v$ for values,
$n$ for numbers, and
$s$ for strings
in the remainder of this text.

The value type must provide arithmetic operations ${+, -, times, div, mod}$
such that every arithmetic operation $arith$ returns a value result, i.e.
$arith: cal(V) -> cal(V) -> cal(R)$.
That means that every arithmetic operation can fail.
Definitions of the arithmetic operators for JSON values are given in @arithmetic.

The value type must also provide Boolean operations
${<, <=, >, >=, eq.quest, eq.not}$, where
$l eq.quest r$ returns whether $l$ equals $r$, and
$l eq.not r$ returns its negation.
Each of these Boolean operations is of type $cal(V) -> cal(V) -> cal(V)$.
The order on JSON values is defined in @json-order.

We assume the existence of several functions:

- $"arr"_0: cal(V)$ yields an empty array.
- $"arr"_1: cal(V) -> cal(V)$ constructs a singleton array from a value.
- $"obj"_0: cal(V)$ yields an empty object.
- $"obj"_1: cal(V) -> cal(V) -> cal(R)$ constructs a singleton object from a key and value.
  (It returns a value result instead of a value because it
  may fail in case that the provided value is not a valid key.)
- $"bool": cal(V) -> bb(B)$ takes a value and returns a boolean.

We use $"arr"_0$ and $"arr"_1$ to define a convenience function $"arr"$
that transforms a list into a value result:
It returns an array if all list elements are values, or into
the first exception in the list otherwise:

$ "sum"&: cal(L) -> cal(V) &&-> cal(R) := lam(l, n) app(l, (lam(h, t) h bindr (lam(o) (n + o bindr app("sum", t)))), (ok(n))) \
  "arr"&: cal(L)           &&-> cal(R) := lam(l) app("sum", (l bind (lam(v) stream(ok((app("arr"_1, v)))))), "arr"_0) $

Here, the function $"sum"$ takes a list $l$ and a zero value $n$ and
returns the sum of the zero value and the list elements if they are all OK,
otherwise it returns the first exception in the list.
This uses the addition operator $+: cal(V) -> cal(V) -> cal(R)$.

Let $p$ a path part (as defined in @syntax) containing values as indices.
We assume two operators:
- The _access operator_ $v[p]$ extracts values contained within $v$
  at positions given by $p$, yielding a list of value results.
  This operator will be used in @semantics and
  is defined for JSON values in @json-access.
- The _update operator_ $v[p]^? update f$ replaces
  those elements $v' = v[p]$ in $v$ by
  the output of $app(f, v')$, where $f: cal(V) -> cal(L)$.
  The update operator yields a single value result.
  This operator will be used in @updates and
  is defined for JSON values in @json-update.

If $v[p]$ returns an error, then
$v[p]  update f$ should yield an error and
$v[p]? update f$ should yield $v$.
We define $v[p]? = v[p] bindl lam(r) app(r, (lam(o) stream(r)), (lam(e) stream()), (lam(b) stream(r)))$.
This simply discards any error yielded by $v[p]$.
