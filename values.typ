#import "common.typ": *

= Values <values>

In this section, we will define values, errors, exceptions, and streams.

While jq has originally been limited to operate on JSON values,
we will define the jq semantics for a general value type.
For this value type, there must be a type of numbers and a type of strings, such that
for any number $n$, $n$ is a value, and
for any string $s$, $s$ is a value.
Furthermore, any boolean $top$ (true) or $bot$ (false) must be a value.
By convention, we will write
$v$ for values,
$n$ for numbers, and
$s$ for strings
in the remainder of this text.
Furthermore, the value type must implement a set of operations that will be given in @value-ops.

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

A _stream_ (or lazy list) is written as $stream(v_0, ..., v_n)$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.
Given some stream $l = stream(x_0, ..., x_n)$, we write
$sum_(x in l) f(x)$ to denote $f(x_0) + ... + f(x_n)$.
We use this frequently to map a function over a stream,
by having $f(x)$ return a stream itself.

In this text, we will see many functions that take values as arguments.
By convention, for any of these functions $f(v_1, ..., v_n)$,
we extend their domain to value results such that $f(v_1, ..., v_n)$ yields $v_i$
(or rather $stream(v_i)$ if $f$ returns streams)
if $v_i$ is an exception and for all $j < i$, $v_j$ is a value.
For example, in @arithmetic, we will define $l + r$ for values $l$ and $r$,
and by our convention, we extend the domain of addition to value results such that
if $l$ is an exception, then $l + r$ returns just $l$, and
if $l$ is a value, but $r$ is an exception, then $l + r$ returns just $r$.

== Value operations <value-ops>

In this subsection, we specify the operations that a value type must implement.

There is a total order $<=$ on values.
We say that $v_1 = v_2$ if and only if both $v_1 <= v_2$ and $v_2 <= v_1$.
For JSON values, this order is given in @json-order.

The function $[dot]$ takes a stream of value results
$stream(v_0, ..., v_n)$ and yields a value result.
If there exists an $i$ such that
$v_i$ is an exception and for all $j < i$, $v_j$ is a value, then
$[stream(v_0, ..., v_n)]$ yields the exception $v_i$, otherwise it yields some value.
For JSON values, $[f]$ constructs an array if all elements of $f$ are values,
see @json-construction.

#example[
  Suppose that 1, 2, and 3 are values.
  Then $[1, "error"(2), "error"(3)] = "error"(2)$.
]

The function ${dot:dot}$ takes a pair of values and yields a value result.
Furthermore, the constant ${}$ yields a value result.
For JSON values, ${s: v}$ constructs a singleton object and ${}$ constructs an empty object,
see @json-construction.

The function $"bool"(v)$ takes a value $v$ and yields a boolean.
If $v in {top, bot}$, then $"bool"(v) = v$.

Let $p$ a path part (as defined in @syntax) containing values as indices.
The _access operator_ $v[p]$ extracts values contained within $v$ at positions given by $p$,
yielding a stream of value results.
The _update operator_ $v[p]^? update f$ replaces those elements $v' = v[p]$ in $v$ by
the output of $f(v')$, where $f$ is a function from a value to a stream of value results.
The update operator yields a single value result.
If $v[p]$ returns an error, then
$v[p]  update f$ should yield an error and
$v[p]? update f$ should yield $v$.
We define $v[p]? = sum_(y in v[p]) cases(
  stream( ) & "if" y = "error"(e),
  stream(y) & "otherwise",
)$.
The access operator will be used in @semantics, and
the update operator will be used in @updates.
For JSON values,
the access operator is defined in @json-access and
the update operator is defined in @json-update.
