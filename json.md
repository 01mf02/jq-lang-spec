\appendix

# JSON values {#sec:json}

In this section, we will define JSON values.
Furthermore, we will define several functions and operations on values.

A JSON value $v$ has the shape
$$v \coloneq \nullf \gror \false \gror \true \gror n \gror s \gror [v_0, ..., v_n] \gror \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n},$$
where $n$ is a number and $s$ is a string.
We write a string $s$ as $c_0...c_n$, where $c$ is a character.
A value of the shape $[v_0, ..., v_n]$ is called an _array_ and
a value of the shape $\obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$ is
an unordered map from _keys_ $k$ to values that we call an _object_.^[
  The JSON syntax uses
  $\obj{k_0: v_0, ..., k_n: v_n}$ instead of
  $\obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$.
  However, in this text, we use the
  $\obj{k_0: v_0, ..., k_n: v_n}$ syntax to denote the _construction_ of objects, and use
  $\obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$ syntax to denote actual objects.
]
In JSON, object keys are strings.^[
  YAML is a data format similar to JSON.
  While YAML can encode any JSON value, it additionally
  allows any YAML values to be used as object keys, where JSON
  allows only strings to be used as object keys.
  This text deliberately distinguishes between object keys and strings.
  That way, extending the given semantics to use YAML values should be relatively easy.
]
We assume that the union of two objects is _right-biased_; i.e.,
if we have two objects $l$ and $r = \obj{k \mapsto v, ...}$, then $(l \cup r)(k) = v$
(regardless of what $l(k)$ might yield).

By convention, we will write in the remainder of this section
$c$ for characters and
$k$ for object keys.
We also write $\err\, ...$ to denote $\err\, e$ where we do not want to specify $e$.
(In actual jq implementations, $e$ is frequently an error message string.)

A number can be an integer or a decimal, optionally followed by an integer exponent.
For example, $0$, $-42$, $3.14$, $3 \times 10^8$ are valid JSON numbers.
This text does not fix how numbers are to be represented,
just like the JSON standard does not impose any representation.^[
  jq uses floating-point numbers to encode both integers and decimals.
  However, several operations in this text (for example those in @sec:json-access)
  make only sense for natural numbers $\mathbb N$ or integers $\mathbb Z$.
  In situations where integer values are expected and a number $n$ is provided,
  jq generally substitutes $n$ by $\floor n$ if $n \geq 0$ and $\ceil n$ if $n < 0$.
  For example, accessing the $0.5$-th element of an array yields its $0$-th element.
  In this text, we use do not document this rounding behaviour for each function.
]
Instead, it just assumes that the type of numbers has a total order (see @sec:json-order) and
supports the arithmetic operations $+$, $-$, $\times$, $\div$, and $\modulo$ (modulo).


## Construction {#sec:json-construction}

In this subsection, we will introduce functions to construct arrays and objects.
\begin{alignat*}{3}
\arr _0:{}&             &&            && \valt \coloneq [] \\
\arr _1:{}&             &&\valt \to{} && \valt \coloneq \lambda v. [v] \\
\objf_0:{}&             &&            && \valt \coloneq \obj{} \\
\objf_1:{}& \valt \to{} &&\valt \to{} && \resultt \coloneq \lambda k\, v. \begin{cases}
  \ok \obj{k \mapsto v} & \text{if $k$ is a string} \\
  \err ... & \text{otherwise}
\end{cases}
\end{alignat*}
In the remainder of this section, we will also use the function
$\arr$ defined in @sec:value-ops based on $\arr_0$ and $\arr_1$.


## Simple functions {#sec:simple-fns}

We are now going to define several functions on values.

The _keys_ of a value are defined as follows:
$$\keys: \valt \to \listt \coloneq \lambda v. \begin{cases}
  \stream{\ok 0, ...,   \ok n} & \text{if } v = [v_0, ..., v_n] \\
  \stream{\ok{k_0}} + \keys\, v' & \text{if } v = \obj{k_0 \mapsto v_0} \cup v' \text{ and } k_0 = \min(\dom(v)) \\
  \stream{} & \text{if } v = {} \\
  \stream{\err ...} & \text{otherwise}
\end{cases}$$
For an object $v$, $\keys\, v$ returns
the domain of the object sorted by ascending order.
For the used ordering, see @sec:json-order.

We define the _length_ of a value as follows:
$$\length: \valt \to \resultt \coloneq \lambda v. \begin{cases}
  \ok 0    & \text{if } v = \nullf \\
  \ok |n|  & \text{if $v$ is a number $n$} \\
  \ok n    & \text{if } v = c_1...c_n \\
  \ok n    & \text{if } v = [v_1, ..., v_n] \\
  \ok n    & \text{if } v = \obj{k_1 \mapsto v_1, ..., k_n \mapsto v_n} \\
  \err ... & \text{otherwise (if $v \in \{\true, \false\}$)}
\end{cases}$$
Here, if $n$ is a number, then
$|n|$ denotes the absolute value of a number, e.g.
$|3.14| = 3.14$ and $|-2| = 2$.
Similarly,
$|s|$ is the number of characters of a string $s$,
$|a|$ is the length of an array $a$, and
$|o|$ is the cardinality of the domain of an object $o$.

The _boolean value_ of a value $v$ is defined as follows:
$$\bool: \valt \to \boolt \coloneq \lambda v. \begin{cases}
  \false & \text{if $v = \nullf$ or $v = \false$} \\
  \true & \text{otherwise}
\end{cases}$$

We can draw a link between the functions here and jq:
When called with the input value $v$,
the jq filter `keys` yields $\stream{\arr\, (\keys\, v)}$,
the jq filter `length` yields $\stream{\length v}$, and
the jq filter `true and .` yields $\stream{\ok (\bool\, v)}$.

## Arithmetic operations {#sec:arithmetic}

We will now define a set of arithmetic operations on values.
We will link these later directly to their counterparts in jq:
Suppose that the jq filters
`f` and `g` yield $\stream l$ and $\stream r$, respectively.
Then the jq filters
`f + g`,
`f - g`,
`f * g`,
`f / g`, and
`f % g` yield
$\stream{l + r}$,
$\stream{l - r}$,
$\stream{l \times r}$,
$\stream{l \div r}$, and
$\stream{l \modulo r}$,
respectively.

### Addition

We define addition of two values $l$ and $r$ as follows:
$$l + r \coloneq \begin{cases}
  \ok v & \text{if $l = \nullf$ and $r = v$, or $l = v$ and $r = \nullf$} \\
  \ok (n_1 + n_2) & \text{if $l$ is a number $n_1$ and $r$ is a number $n_2$} \\
  \ok (c_{l,1}...c_{l,m}c_{r,1}...c_{r,n}) & \text{if $l = c_{l,1}...c_{l,m}$ and $r = c_{r,1}...c_{r,n}$} \\
  \ok [l_1, ..., l_m, r_1, ..., r_n] & \text{if $l = [l_1, ..., l_m]$ and $r = [r_1, ..., r_n]$} \\
  \ok (l \cup r) & \text{if $l = \obj{...}$ and $r = \obj{...}$} \\
  \err ... & \text{otherwise}
\end{cases}$$
Here, we can see that $\nullf$ serves as a neutral element for addition.
For strings and arrays, addition corresponds to their concatenation, and
for objects, it corresponds to their union.

### Multiplication

Given two objects $l$ and $r$, we define their _recursive merge_ $l \Cup r$ as:
$$l \Cup r \coloneq \begin{cases}
  {k \mapsto v_l \Cup v_r} \cup l' \Cup r' & \text{if $l = \obj{k \mapsto v_l} \cup l'$, $r = \obj{k \mapsto v_r} \cup r'$, and $v_l, v_r$ are objects} \\
  \obj{k \mapsto v_r} \cup l' \Cup r' & \text{if $l = {k \mapsto v_l} \cup l'$, $r = \obj{k \mapsto v_r} \cup r'$, and $v_l$ or $v_r$ is not an object} \\
  \obj{k \mapsto v_r} \cup l \Cup r' & \text{if $k \notin \dom(l)$ and $r = \obj{k \mapsto v_r} \cup r'$} \\
  l & \text{otherwise (if $r = \obj{}$)}
\end{cases}$$

We use $\Cup$ in the following definition of multiplication of two values $l$ and $r$:
$$l \times r \coloneq \begin{cases}
  \ok(n_1 \times n_2) & \text{if $l$ is a number $n_1$ and $r$ is a number $n_2$} \\
  \sum_{i = 1}^n s & \text{if $l$ is a string $s$ and $r$ is a number $n \in \mathbb Z$} \\
  r \times l & \text{if $r$ is a string and $l \in \mathbb Z$} \\
  \ok(l \Cup r) & \text{if $l$ and $r$ are objects} \\
  \err ... & \text{otherwise}
\end{cases}$$
We can see that for a string $s$ and an integer $n$,
their multiplication $s \times n$ yields
the concatenation of $n$ times the string $s$ if $n > 0$ and
$\nullf$ if $n \leq 0$ (because $\nullf$ is the neutral element for addition).
The multiplication of two objects corresponds to their recursive merge as defined above.

### Subtraction

We now define subtraction of two values $l$ and $r$:
$$l - r \coloneq \begin{cases}
  \ok(n_1 - n_2) & \text{if $l$ is a number $n_1$ and $r$ is a number $n_2$} \\
  \arr (\sum_{i, l_i \notin \{r_0, ..., r_n\}} \stream{\ok l_i}) & \text{if $l = [l_0, ..., l_n]$ and $r = [r_0, ..., r_n]$} \\
  \err ... & \text{otherwise}
\end{cases}$$
When both $l$ and $r$ are arrays, then $l - r$ returns
an array containing those values of $l$ that are not contained in $r$.

### Division

\newcommand{\splitf}{\operatorname{split}}
We will now define a function that
splits a string $y + x$ by some non-empty separator string $s$.
The function preserves the invariant that $y$ does not contain $s$:
$$\splitf \coloneq \lambda x\, s\, y. \begin{cases}
  \splitf\, (c_1...c_n)\, s\, (y + c_0) & \text{if $x = c_0...c_n$ and $c_0...c_{|s| - 1} \neq s$} \\
  [y] + \splitf\, (c_{|s|}...c_n)\, s\, "" & \text{if $x = c_0...c_n$ and $c_0...c_{|s| - 1} = s$} \\
  [y] & \text{otherwise ($|x| = 0$)}
\end{cases}$$

We use this splitting function to define division of two values:

$$l \div r \coloneq \begin{cases}
  \ok(n_1 \div n_2) & \text{if $l$ is a number $n_1$ and $r$ is a number $n_2$} \\
  \ok [] & \text{if $l$ and $r$ are strings and $|l| = 0$} \\
  \arr (\sum_i \stream{\ok c_i}) & \text{if $l = c_0...c_n$, $r$ is a string, $|l| > 0$, and $|r| = 0$} \\
  \ok(\splitf\, l\, r\, "") & \text{if $l$ and $r$ are strings, $|l| > 0$, and $|r| > 0$} \\
  \err ... & \text{otherwise}
\end{cases}$$

::: {.example}
  Let $s = "ab"$.
  We have that
  $s \div s = ["", ""]$.
  Furthermore,
  $"c" \div s = ["c"]$,
  $(s + "c" + s           ) \div s = ["", "c", ""  ]$ and
  $(s + "c" + s + "de") \div s = ["", "c", "de"]$.
:::

From this example, we can infer the following lemma.

::: {.lemma}
  Let $l$ and $r$ strings with $|l| > 0$ and $|r| > 0$.
  Then $l \div r = [l_0, ..., l_n]$ for some $n > 0$ such that
  $l = (\sum_{i = 0}^{n - 1} (l_i + r)) + l_n$ and
  for all $i$, $l_i$ is a string that does not contain $r$ as substring.
:::

### Remainder

For two values $l$ and $r$, the arithmetic operation
$l \modulo r$ (modulo) yields
$m \modulo n$ if $l$ and $r$ are numbers $m$ and $n$,
otherwise it yields an error.


## Accessing {#sec:json-access}

We will now define _access operators_.
These serve to extract values that are contained within other values.

The value $v[i]$ of a value $v$ at index $i$ is defined as follows:

$$v[i] \coloneq \begin{cases}
  \ok v_i    & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb N$, and $i \leq n$} \\
  \ok \nullf & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb N$, and $i > n$} \\
  v[n+i]     & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+i$} \\
  \ok v_j    & \text{if $v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$, $i$ is a string, and $k_j = i$} \\
  \ok \nullf & \text{if $v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$, $i$ is a string, and $i \notin \{k_0, ..., k_n\}$} \\
  \err ...  & \text{otherwise}
\end{cases}$$

The idea behind this index operator is as follows:
It returns $\nullf$ if
the value $v$ does not contain a value at index $i$,
but $v$ could be _extended_ to contain one.
More formally, $v[i]$ is $\nullf$ if $v \neq \nullf$ and
there exists some value $v' = v + \delta$ such that $v'[i] \neq \nullf$.

The behaviour of this operator for $i < 0$ is that $v[i]$ equals $v[|v| + i]$.

::: {.example}
  If $v = [0, 1, 2]$, then $v[1] = 1$ and $v[-1] = v[3 - 1] = 2$.
:::

Using the index operator, we can define the values $v[]$ in a value $v$ as follows:
$$v[] \coloneq \keys v \bind \lambda k. \stream{v[k]}$$
When provided with
an array $v = [v_0, ..., v_n]$ or
an object $v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$
(where $k_0 < ... < k_n$),
$v[]$ returns the stream $\stream{\ok v_0, ..., \ok v_n}$.

Next, we define a slice operator:
$$v[i:j] \coloneq \begin{cases}
  \ok [v_i, ..., v_{j-1}] & \text{if $v = [v_0, ..., v_n]$ and $i, j \in \mathbb N$} \\
  \ok (c_i  ...  c_{j-1}) & \text{if $v =  c_0  ...  c_n $ and $i, j \in \mathbb N$} \\
  v[(n+i):j] & \text{if $|v| = n$, $i \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+i$} \\
  v[i:(n+j)] & \text{if $|v| = n$, $j \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+j$} \\
  \err ... & \text{otherwise}
\end{cases}$$
Note that unlike $v[]$ and $v[i]$, $v[i:j]$ may yield a value if $v$ is a string.
If we have that $i, j \in \mathbb N$ and either $i > n$ or $i \geq j$, then $v[i:j]$ yields
an empty array  if $v$ is an array, and
an empty string if $v$ is a string.

::: {.example}
  If $v = [0, 1, 2, 3]$, then $v[1:3] = [1, 2]$.
:::


@sec:value-ops demands all access operators to yield a _stream_ of value results, yet only
$v[]$ fulfills this, whereas $v[i]$ and $v[i:j]$ return a single value result.
For that reason, we now redefine these operators to return a stream of value results, by
\begin{align*}
v[i]   &\coloneq \stream{v[i]} \\
v[i:j] &\coloneq \stream{v[i:j]}
\end{align*}
Finally, we define the remaining access operators by using the slice operator:
\begin{alignat*}{4}
v[:j] &\coloneq                                       && v[0 &&: &j&] \\
v[i:] &\coloneq \stream{\length\, v} \bind \lambda l. && v[i &&: &l&]
\end{alignat*}

When $\length\, v$ yields an error, then $v[i:]$ yields an error, too.


## Updating {#sec:json-update}

For each access operator in @sec:json-access, we will now define an _updating_ counterpart.
Intuitively, where an access operator yields some elements contained in a value $v$,
its corresponding update operator _replaces_ these elements in $v$
by the output of a function.
The access operators will be used in @sec:semantics, and
the update operators will be used in @sec:updates.

All update operators take at least
a value $v: \valt$ and a function $f: \valt \to \listt$, and return a value result.

\newcommand{\objif}{\operatorname{obj\_if}}
The first update operator will be a counterpart to $v[]$.
For all elements $x$ that are yielded by $v[]$,
$v[] \update f$ replaces $x$ by $f(x)$:
$$v[] \update f \coloneq \begin{cases}
  \arr (\sum_i f(v_i)) & \text{if } v = [v_0, ..., v_n] \\
  \sumf\, (\keys v \bind \lambda k. v[k] \bind \lambda v. \stream{\objif\, k\, (f\, v)})\, \obj{} & \text{if $v$ is an object} \\
  \err ... & \text{otherwise}
\end{cases}$$

Here, we use the function $\sumf$ from @sec:value-ops as well as
a helper function for the case that $v$ is an object.
This function takes an object key $k$ and $s: \listt$ and returns a value result:
$$\objif \coloneq \lambda k\, s. s\, (\lambda h\, t. h \bindr \lambda o. \ok \obj{k \mapsto o})\, (\ok \obj{})$$

For an input array $v = [v_0, ..., v_n]$,
$v[] \update f$ replaces each $v_i$ by the output of $f(v_i)$, yielding
$[f(v_0)] + ... + [f(v_n)]$.
For an input object $v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$,
$v[] \update f$ replaces each $v_i$ by the first output yielded by $f(v_i)$ if such an output exists,
otherwise it deletes $\obj{k_i \mapsto v_i}$ from the object.
Note that updating arrays diverges from jq, because
jq only considers the first value yielded by $f$.

\newcommand{\cut}{\operatorname{cut}}
For the next operators, we will use the following function
$\cut\, v\, i\, j\, n\, s$, which
replaces the slice $[i:j]$ of an array $v$ of length $n$ by a stream $s$:
$$\cut \coloneq \lambda v\, i\, j\, n\, s. \sumf\, (v[0:i] + s + v[j:n])\, []$$

The next operator replaces the $i$-th element of a value $v$ by the outputs of $f$:
$$v[i] \update f \coloneq \begin{cases}
  \cut\, v\, i\, (i+1)\, n\, \stream{\arr (f v_i)} & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb N$, and $i \leq n$} \\
  v[n+i] \update f & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+i$} \\
  \objif\, i\, (f\, v') \bindr \lambda y. y + o & \text{if } v = \obj{i \mapsto v'} \cup o \\
  \err ... & \text{otherwise}
\end{cases}$$
Note that this diverges from jq if $v = [v_0, ..., v_n]$ and $i > n$,
because jq fills up the array with $\nullf$.

<!--
but we unfortunately cannot use it to define {k: f}, because if f returns the empty list,
we cannot provide a default element e that would make the key disappear
-->

The final operator is the update counterpart of the operator $v[i:j]$.
It replaces the slice $v[i:j]$ by the concatenation of the outputs of $f$ on $v[i:j]$.
$$v[i:j] \update f \coloneq \begin{cases}
  \cut\, v\, i\, j\, n\, (v[i:j] >>= f) & \text{if $v = [v_0, ..., v_n],$ $i, j \in \mathbb N$, and $i \leq j$} \\
  \ok v & \text{if $v = [v_0, ..., v_n]$, $i, j \in \mathbb N$, and $i > j$} \\
  v[(n+i):j] \update f & \text{if $|v| = n$, $i \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+i$} \\
  v[i:(n+j)] \update f & \text{if $|v| = n$, $j \in \mathbb Z \setminus \mathbb N$, and $0 \leq n+j$} \\
  \err ... & \text{otherwise}
\end{cases}$$
Unlike its corresponding access operator $v[i:j]$,
this operator unconditionally fails when $v$ is a string.
This operator diverges from jq if $f$ yields $\nullf$, in which case
jq returns an error, whereas
this operator treats this as equivalent to $f$ returning $[]$.
Both $v[i] \update f$ and $v[i:j] \update f$ diverge from jq when
$f$ returns multiple values, in which case jq considers only the first output of $f$.

::: {.example}
  If $v = [0, 1, 2, 3]$ and $f = \lambda v. [4, 5, 6]$, then $v[1:3] \update f = [0, 4, 5, 6, 3]$.
:::

Similarly to @sec:json-access, we define the remaining operators by $v[i:j]$:
\begin{alignat*}{3}
v[:j] \update f &\coloneq                             && v[0:&j] \update f \\
v[i:] \update f &\coloneq \length v \bindr \lambda l. && v[i:&l] \update f
\end{alignat*}


## Order {#sec:json-order}

In this subsection, we establish a total order on values.

<!-- TODO: total order is <=, not < ! -->

\newcommand{\nan}{\operatorname{nan}}
We have that
$$\nullf < \false < \true < n < s < a < o,$$ where
$n$ is a number,
$s$ is a string,
$a$ is an array, and
$o$ is an object.
We assume that there is a total order on numbers and characters.
jq does _not_ implement a _strict_ total order on values;
in particular, its order on (floating-point) numbers specifies $\nan < \nan$,
from which follows that $\nan \neq \nan$ and $\nan \ngtr \nan$.
Strings and arrays are ordered lexicographically.

Two objects $o_1$ and $o_2$ are ordered as follows:
For both objects $o_i$ ($i \in \{1, 2\}$),
we sort the array $[\keys\, o_i]$ by ascending order to obtain the ordered array of keys
$k_i = [k_1, ..., k_n]$, from which we obtain
$v_i = [o[k_1], ..., o[k_n]]$.
We then have $$o_1 < o_2 \iff \begin{cases}
  k_1 < k_2 & \text{if $k_1 < k_2$ or $k_1 > k_2$} \\
  v_1 < v_2 & \text{otherwise ($k_1 = k_2$)}
\end{cases}$$
