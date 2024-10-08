#import "common.typ": *

= JSON values <json>

In this section, we will define JSON values.
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
  However, in this text, we use the
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

By convention, we will write in the remainder of this section
$c$ for characters and
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
  However, several operations in this text (for example those in @json-access)
  make only sense for natural numbers $NN$ or integers $ZZ$.
  In situations where integer values are expected and a number $n$ is provided,
  jq generally substitutes $n$ by $floor(n)$ if $n >= 0$ and $ceil(n)$ if $n < 0$.
  For example, accessing the $0.5$-th element of an array yields its $0$-th element.
  In this text, we use do not document this rounding behaviour for each function.
]
Instead, it just assumes that the type of numbers has a total order (see @json-order) and
supports the arithmetic operations $+$, $-$, $times$, $div$, and $mod$ (modulo).


== Construction <json-construction>

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
For the used ordering, see @json-order.

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

We will now define a set of arithmetic operations on values.
We will link these later directly to their counterparts in jq:
Suppose that the jq filters
`f` and `g` yield $stream(l)$ and $stream(r)$, respectively.
Then the jq filters
`f + g`,
`f - g`,
`f * g`,
`f / g`, and
`f % g` yield
$stream(l + r)$,
$stream(l - r)$,
$stream(l times r)$,
$stream(l div r)$, and
$stream(l mod r)$,
respectively.

=== Addition

We define addition of two values $l$ and $r$ as follows:

$ l + r := cases(
  v & "if" l = "null" "and" r = v", or" l = v "and" r = "null",
  n_1 + n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  c_(l,1)...c_(l,m)c_(r,1)...c_(r,n) & "if" l = c_(l,1)...c_(l,m) "and" r = c_(r,1)...c_(r,n),
  [stream(l_1, ..., l_m, r_1, ..., r_n)] & "if" l = [l_1, ..., l_m] "and" r = [r_1, ..., r_n],
  l union r & "if" l = {...} "and" r = {...},
  "error" & "otherwise",
) $

Here, we can see that $"null"$ serves as a neutral element for addition.
For strings and arrays, addition corresponds to their concatenation, and
for objects, it corresponds to their union.

=== Multiplication

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

=== Subtraction

We now define subtraction of two values $l$ and $r$:

$ l - r := cases(
  n_1 - n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  [sum_(i, l_i in {r_0, ..., r_n}) stream(l_i) ] & "if" l = [l_0, ..., l_n] "and" r = [r_0, ..., r_n],
  "error" & "otherwise"
) $

When both $l$ and $r$ are arrays, then $l - r$ returns
an array containing those values of $l$ that are not contained in $r$.

=== Division

We will now define a function that
splits a string $y + x$ by some non-empty separator string $s$.
The function preserves the invariant that $y$ does not contain $s$:

$ "split"(x, s, y) := cases(
  "split"(c_1...c_n, s, y + c_0) & "if" x = c_0...c_n "and" c_0...c_(|s| - 1) != s,
  [stream(y)] + "split"(c_(|s|)...c_n, s, qs("")) & "if" x = c_0...c_n "and" c_0...c_(|s| - 1) = s,
  [stream(y)] & "otherwise" (|x| = 0),
) $

We use this splitting function to define division of two values:

$ l div r := cases(
  n_1 div n_2 & "if" l "is a number" n_1 "and" r "is a number" n_2,
  [] & "if" l "and" r "are strings and " |l| = 0,
  [sum_i stream(c_i)] & "if" l = c_0...c_n "," r "is a string," |l| > 0", and" |r| = 0,
  "split"(l, r, qs("")) & "if" l "and" r "are strings," |l| > 0", and" |r| > 0,
  "error" & "otherwise"
) $

#example[
  Let $s = qs("ab")$.
  We have that
  $s div s = [qs(""), qs("")]$.
  Furthermore,
  $qs("c") div s = [qs("c")]$,
  $(s + qs("c") + s           ) div s = [qs(""), qs("c"), qs("")  ]$ and
  $(s + qs("c") + s + qs("de")) div s = [qs(""), qs("c"), qs("de")]$.
]

From this example, we can infer the following lemma.

#lemma[
  Let $l$ and $r$ strings with $|l| > 0$ and $|r| > 0$.
  Then $l div r = [l_0, ..., l_n]$ for some $n > 0$ such that
  $l = (sum_(i = 0)^(n - 1) (l_i + r)) + l_n$ and
  for all $i$, $l_i$ is a string that does not contain $r$ as substring.
]

=== Remainder

For two values $l$ and $r$, the arithmetic operation
$l mod r$ (modulo) yields
$m mod n$ if $l$ and $r$ are numbers $m$ and $n$,
otherwise it yields an error.


== Accessing <json-access>

We will now define _access operators_.
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

Next, we define a slice operator:

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


@value-ops demands all access operators to yield a _stream_ of value results, yet only
$v[]$ fulfills this, whereas $v[i]$ and $v[i:j]$ return a single value result.
For that reason, we now redefine these operators to return a stream of value results, by
$ v[i]   &:= stream(v[i]) \
  v[i:j] &:= stream(v[i:j]) $

Finally, we define the remaining access operators by using the slice operator:

$ v[:j] &:= v[0:  &j] \
  v[i:] &:= v[i:&|v|] $

When $|v|$ yields an error, then $v[i:]$ yields an error, too.


== Updating <json-update>

For each access operator in @json-access, we will now define an _updating_ counterpart.
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

Similarly to @json-access, we define the remaining operators by $v[i:j]$:

$ v[:j] update f &:= v[0:  &j] update f \
  v[i:] update f &:= v[i:&|v|] update f $


== Order <json-order>

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
