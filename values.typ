#import "common.typ": *

= Values <values>

In this section, we will define
JSON values, errors, exceptions, and streams.
Furthermore, we will define several functions and operations on values.

A JSON value $v$ has the shape

$ v := "null" #or_ "false" #or_ "true" #or_ n #or_ s #or_ [v_0, ..., v_n] #or_ {k_0 |-> v_0, ..., k_n |-> v_n}, $

where $n$ is a number and $s$ is a string.
We write a string $s$ as $c_0...c_n$, where $c$ is a character.
A value of the shape $[v_0, ..., v_n]$ is called an _array_ and
a value of the shape ${k_0 |-> v_0, ..., k_n |-> v_n}$ is
an unordered map from _keys_ $k$ to values that we call an _object_.#footnote[
  The JSON syntax uses
  ${k_0: v_0, ..., k_n: v_n}$ instead of
  ${k_0 |-> v_0, ..., k_n |-> v_n}$.
  However, in this text, we will use the
  ${k_0: v_0, ..., k_n: v_n}$ syntax to denote the _construction_ of objects, and use
  ${k_0 |-> v_0, ..., k_n |-> v_n}$ syntax to denote actual objects.
]
In JSON, object keys are strings.#footnote[
  YAML is a data format similar to JSON.
  While YAML can encode any JSON value, it additionally
  allows any YAML values to be used as object keys, where JSON
  allows only strings to be used as object keys.
  This text deliberately distinguishes between object keys and strings.
  That way, extending the given semantics to use YAML values should be relatively easy.
]
We assume that the union of two objects is _right-biased_; i.e.,
if we have two objects $l$ and $r = {k |-> v, ...}$, then $(l union r)(k) = v$
(regardless of what $l(k)$ might yield).

By convention, we will write in the remainder of this text
$v$ for values,
$n$ for numbers,
$c$ for characters, and
$k$ for object keys.
We will sometimes write arrays as $[v_0, ..., v_n]$ and sometimes as $[v_1, ..., v_n]$:
The former case is useful to express that $n$ is the maximal index of the array (having length $n+1$), and
the latter case is useful to express that the array has length $n$.
The same idea applies also to strings, objects, and streams.

A number can be an integer or a decimal, optionally followed by an integer exponent.
For example, $0$, $-42$, $3.14$, $3 times 10^8$ are valid JSON numbers.
This text does not fix how numbers are to be represented,
just like the JSON standard does not impose any representation.#footnote[
  jq uses floating-point numbers to encode both integers and decimals.
  However, several operations in this text (for example those in @accessing)
  make only sense for natural numbers $NN$ or integers $ZZ$.
  In situations where integer values are expected and a number $n$ is provided,
  jq generally substitutes $n$ by $floor(n)$ if $n >= 0$ and $ceil(n)$ if $n < 0$.
  For example, accessing the $0.5$-th element of an array yields its $0$-th element.
  In this text, we use do not document this rounding behaviour for each function.
]
Instead, it just assumes that the type of numbers has a total order (see @ordering) and
supports the arithmetic operations $+$, $-$, $times$, $div$, and $mod$ (modulo).

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



== Construction <construction>

In this subsection, we will introduce operators to construct arrays and objects.

The function $[dot]$ transforms a stream into
an array if all stream elements are values, or into
the first exception in the stream otherwise:

$ [stream(v_0, ..., v_n)] := cases(
  v_i & "if" v_i "is an exception and for all" j < i", " v_j "is a value",
  [v_0, ..., v_n] & "otherwise",
) $

Given two values $k$ and $v$, we can make an object out of them:

$ {k: v} := cases(
  {k |-> v} & "if" k "is a string and" v "is a value",
  "error" & "otherwise",
) $

We can construct objects with multiple keys by adding objects, see @arithmetic.


== Simple functions <simple-fns>

We are now going to define several functions that take a value and return a value.

The _keys_ of a value are defined as follows:

$ "keys"(v) := cases(
  stream(0  , ...,   n) & "if" v = [v_0, ..., v_n],
  stream(k_0) + "keys"(v') & "if" v = {k_0 |-> v_0} union v' "and" k_0 = min("dom"(v)),
  stream() & "if" v = {},
  stream("error") & "otherwise",
) $

For an object $v$, $"keys"(v)$ returns
the domain of the object sorted by ascending order.
For the used ordering, see @ordering.

We define the _length_ of a value as follows:

$ |v| := cases(
  0       & "if" v = "null",
  |n|     & "if" v "is a number" n,
  n       & "if" v = c_1...c_n,
  n       & "if" v = [v_1, ..., v_n],
  n       & "if" v = {k_1 |-> v_1, ..., k_n |-> v_n},
  "error" & "otherwise (if" v in {"true", "false"}")",
) $

The _boolean value_ of a value $v$ is defined as follows:

$ "bool"(v) := cases(
  "false" & "if" v = "null" "or" v = "false",
  "true" & "otherwise",
) $

We can draw a link between the functions here and jq:
When called with the input value $v$,
the jq filter `keys` yields $stream(["keys"(v)])$,
the jq filter `length` yields $stream(|v|)$, and
the jq filter `true and .` yields $stream("bool"(v))$.

== Arithmetic operations <arithmetic>

We define addition of two values $l$ and $r$ as follows:

$ l + r := cases(
  v & "if" l = "null" "and" r = v", or" l = v "and" r = "null",
  n_1 + n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  c_(l,1)...c_(l,m)c_(r,1)...c_(r,n) & "if" l = c_(l,1)...c_(l,m) "and" r = c_(r,1)...c_(r,n),
  [l_1, ..., l_m, r_1, ..., r_n] & "if" l = [l_1, ..., l_m] "and" r = [r_1, ..., r_n],
  l union r & "if" l = {...} "and" r = {...},
  "error" & "otherwise",
) $

Here, we can see that $"null"$ serves as a neutral element for addition.
For strings and arrays, addition corresponds to their concatenation, and
for objects, it corresponds to their union.

#let merge = $union.double$
Given two objects $l$ and $r$, we define their _recursive merge_ $l merge r$ as:

$ l merge r := cases(
  {k |-> v_l merge v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l"," v_r "are objects",
  {k |-> v_r} union l' merge r' & "if" l = {k |-> v_l} union l'"," r = {k |-> v_r} union r'", and" v_l "or" v_r "is not an object",
  {k |-> v_r} union l merge r' & "if" k in.not "dom"(l) "and" r = {k |-> v_r} union r',
  l & "otherwise (if" r = {} ")",
) $

We use this in the following definition of multiplication of two values $l$ and $r$:

$ l times r := cases(
  n_1 times n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  l + l times (r - 1) & "if" l "is a string and" r in NN without {0},
  "null" & "if" l "is a string and" r = 0,
  r times l & "if" r "is a string and" l in NN,
  l merge r & "if" l "and" r "are objects",
  "error" & "otherwise"
) $

We can see that multiplication of a string $s$ with a natural number $n > 0$ returns
$sum_(i = 1)^n s$; that is, the concatenation of $n$ times the string $s$.
The multiplication of two objects corresponds to their recursive merge as defined above.

For two values $l$ and $r$, the arithmetic operations
$l - r$, $l div r$, and $l mod r$ (modulo) yield
$m - n$, $m div n$, and $m mod n$ if $l$ and $r$ are numbers $m$ and $n$,
otherwise they yield an error.

Suppose that the jq filters
`f` and `g` yield $stream(l)$ and $stream(r)$, respectively.
Then the jq filters `f + g` and `f * g` yield
$stream(l + r)$ and $stream(l times r)$, respectively.


== Accessing <accessing>

We will now define three _access operators_.
These serve to extract values that are contained within other values.

The value $v[i]$ of a value $v$ at index $i$ is defined as follows:

$ v[i] := cases(
  v_i    & "if" v = [v_0, ..., v_n] "," i in NN", and" i <= n,
  "null" & "if" v = [v_0, ..., v_n] "," i in NN", and" i > n,
  v[n+i] & "if" v = [v_0, ..., v_n] "," i in ZZ without NN", and" 0 <= n+i,
  v_j    & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" k_j = i,
  "null" & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n}"," i "is a string, and" i in.not {k_0, ..., k_n},
  "error" & "otherwise",
) $

The idea behind this index operator is as follows:
It returns $"null"$ if
the value $v$ does not contain a value at index $i$,
but $v$ could be _extended_ to contain one.
More formally, $v[i]$ is $"null"$ if $v != "null"$ and
there exists some value $v' = v + delta$ such that $v'[i] != "null"$.

The behaviour of this operator for $i < 0$ is that $v[i]$ equals $v[abs(v) + i]$.

#example[
  If $v = [0, 1, 2]$, then $v[1] = 1$ and $v[-1] = v[3 - 1] = 2$.
]

Using the index operator, we can define the values $v[]$ in a value $v$ as follows:

$ v[] := sum_(i in"keys"(v)) stream(v[i]) $

When provided with
an array $v = [v_0, ..., v_n]$ or
an object $v = {k_0 |-> v_0, ..., k_n |-> v_n}$ (where $k_0 < ... < k_n$),
$v[]$ returns the stream $stream(v_0, ..., v_n)$.

The last operator that we define here is a slice operator:

$ v[i:j] := cases(
  [sum_(k = i)^(j-1) stream(v_k)] & "if" v = [v_0, ..., v_n] "and" i","j in NN,
  sum_(k = i)^(j-1) c_k & "if" v = c_0...c_n "and" i","j in NN,
  v[(n+i):j] & "if" |v| = n", " i in ZZ without NN", and" 0 <= n+i,
  v[i:(n+j)] & "if" |v| = n", " j in ZZ without NN", and" 0 <= n+j,
  "error" & "otherwise",
) $

Note that unlike $v[]$ and $v[i]$, $v[i:j]$ may yield a value if $v$ is a string.
If we have that $i, j in NN$ and either $i > n$ or $i >= j$, then $v[i:j]$ yields
an empty array  if $v$ is an array, and
an empty string if $v$ is a string.

#example[
  If $v = [0, 1, 2, 3]$, then $v[1:3] = [1, 2]$.
]

The operator $v[]$ is the only operator in this subsection that
returns a _stream_ of value results instead of only a value result.


== Updating <updating>

For each access operator in @accessing, we will now define an _updating_ counterpart.
Intuitively, where an access operator yields some elements contained in a value $v$,
its corresponding update operator _replaces_ these elements in $v$
by the output of a function.
The access operators will be used in @semantics, and
the update operators will be used in @updates.

All update operators take at least
a value $v$ and
a function $f$ from a value to a stream of value results.
We extend the domain of $f$ to value results such that
$f(e) = stream(e)$ if $e$ is an exception.

The first update operator will be a counterpart to $v[]$.
For all elements $x$ that are yielded by $v[]$,
$v[] update f$ replaces $x$ by $f(x)$:

$ v[] update f := cases(
  [sum_i f(v_i)] & "if" v = [v_0, ..., v_n],
  union.big_i cases({k_i : h} & "if" f(v_i) = stream(h) + t, {} & "otherwise") & "if" v = {k_0 |-> v_0, ..., k_n |-> v_n},
  "error" & "otherwise",
) $

For an input array $v = [v_0, ..., v_n]$,
$v[] update f$ replaces each $v_i$ by the output of $f(v_i)$, yielding
$[f(v_0) + ... + f(v_n)]$.
For an input object $v = {k_0 |-> v_0, ..., k_n |-> v_n}$,
$v[] update f$ replaces each $v_i$ by the first output yielded by $f(v_i)$ if such an output exists,
otherwise it deletes ${k_i |-> v_i}$ from the object.
Note that updating arrays diverges from jq, because
jq only considers the first value yielded by $f$.

For the next operators, we will use the following function $"head"(l, e)$, which
returns the head of a list $l$ if it is not empty, otherwise $e$:

$ "head"(l, e) := cases(
  h & "if" l = stream(h) + t,
  e & "otherwise",
) $

The next function takes a value $v$ and
replaces its $i$-th element by the first output of $f$,
or deletes it if $f$ yields no output:
$ v[i] update f := cases(
  v[0:i] + ["head"(f(v[i]), stream())] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN", and" i <= n,
  /*
  v[0:i] + [h] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN"," i <= n", and" f(v[i]) = stream(h) + t,
  v[0:i] + v[(i+1):n]
    & "if" v = [v_0, ..., v_n]", " i in NN"," i <= n", and" f(v[i]) = stream(),
  */
  v[n+i] update f & "if" v = [v_0, ..., v_n]", " i in ZZ without NN", and" 0 <= n+i,
  v + {i: h} & "if" v = {...} "and" f(v[i]) = stream(h) + t,
  union.big_(k in "dom"(v) without {i}) {k |-> v[k]} & "if" v = {...} "and" f(v[i]) = stream(),

  "error" & "otherwise",
) $

Note that this diverges from jq if $v = [v_0, ..., v_n]$ and $i > n$,
because jq fills up the array with $"null"$.

// but we unfortunately cannot use it to define {k: f}, because if f returns the empty list,
// we cannot provide a default element e that would make the key disappear

The final function here is the update counterpart of the operator $v[i:j]$.
It replaces the slice $v[i:j]$
by the first output of $f$ on $v[i:j]$, or
by the empty array if $f$ yields no output.
$ v[i:j] update f := cases(
  v[0:i] + "head"(f(v[i:j]), []) + v[j:n] & "if" v = [v_0, ..., v_n]", " i","j in NN", and" i <= j,
  v & "if" v = [v_0, ..., v_n]", " i","j in NN", and" i > j,
  v[(n+i):j] update f & "if" |v| = n", " i in ZZ without NN", and" 0 <= n+i,
  v[i:(n+j)] update f & "if" |v| = n", " j in ZZ without NN", and" 0 <= n+j,
  "error" & "otherwise",
) $

Unlike its corresponding access operator $v[i:j]$,
this operator unconditionally fails when $v$ is a string.
This operator diverges from jq if $f$ yields $"null"$, in which case
jq returns an error, whereas
this operator treats this as equivalent to $f$ returning $[]$.

#example[
  If $v = [0, 1, 2, 3]$ and $f(v) = [4, 5, 6]$, then $v[1:3] update f = [0, 4, 5, 6, 3]$.
]

== Ordering <ordering>

In this subsection, we establish a total order on values.#footnote[
  Note that jq does _not_ implement a _strict_ total order on values;
  in particular, its order on (floating-point) numbers specifies $"nan" < "nan"$,
  from which follows that $"nan" != "nan"$ and $"nan" gt.not "nan"$.
]

We have that
$ "null" < "false" < "true" < n < s < a < o, $ where
$n$ is a number,
$s$ is a string,
$a$ is an array, and
$o$ is an object.
We assume that there is a total order on numbers and characters.
Strings and arrays are ordered lexicographically.

Two objects $o_1$ and $o_2$ are ordered as follows:
For both objects $o_i$ ($i in {1, 2}$),
we sort the array $["keys"(o_i)]$ by ascending order to obtain the ordered array of keys
$k_i = [k_1, ..., k_n]$, from which we obtain
$v_i = [o[k_1], ..., o[k_n]]$.
We then have $ o_1 < o_2 <==> cases(
  k_1 < k_2 & "if" k_1 < k_2 "or" k_1 > k_2,
  v_1 < v_2 & "otherwise" (k_1 = k_2)
) $
