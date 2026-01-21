# Values {#sec:values}

In this section, we define several data types, such as
values, results, and lists, in simply typed lambda calculus.

While jq operates uniquely on JSON values,
we define the jq semantics for a general value type $\valt$.
This value type must satisfy several properties that will be given in @sec:value-ops.

\newcommand{\some}{\operatorname{some}}
\newcommand{\none}{\operatorname{none}}
\newcommand{\fst}{\operatorname{fst}}
\newcommand{\snd}{\operatorname{snd}}

We use letters such as $T$, $U$, $X$, and $Y$ for type variables.
Let us fix some standard encodings for
boolean values $\boolt$,
natural numbers $\mathbb N$,
optional values $\optt\, T$,
lists $\stream T$, and
pairs $(T, U)$:
\begin{alignat*}{2}
\true &: \boolt &&\coloneqq \lambda t\, f. t \\
\false&: \boolt &&\coloneqq \lambda t\, f. f \\
\succf&: \mathbb N \to \mathbb N &&\coloneqq \lambda n\, s\, z. s\, n \\
\zero&: \mathbb N &&\coloneqq \lambda s\, z. z \\
\some&: T \to \optt\,T &&\coloneqq \lambda x\, s\, n. s\, x \\
\none&: \optt\,T &&\coloneqq \lambda s\, n. n \\
\cons&: T \to \stream T \to \stream T &&\coloneqq \lambda h\, t. \lambda c\, n. c\, h\, t \\
\nil&: \stream T &&\coloneqq \lambda c\, n. n \\
\pair&{}: T \to U \to (T, U) &&\coloneqq \lambda x\, y\, p. p\, x\, y  \\
\fst&{}: (T, U) \to T &&\coloneqq \lambda p. p\, (\lambda x\, y. x) \\
\snd&{}: (T, U) \to T &&\coloneqq \lambda p. p\, (\lambda x\, y. y)
\end{alignat*}

We use natural numbers to store label identifiers.
We can construct a function
$\nateq: \mathbb N \to \mathbb N \to \boolt$ that returns
$\true$ if two natural numbers are equal, else $\false$.

We write the empty list
$\nil$ as $\stream{}$ and
$\cons\, r_1\, (\cons\, r_2\, ...)$ as $\stream{r_1, r_2, ...}$.
Because the jq language is evaluated lazily, lists can be infinite.

The elements returned by jq filters are _value results_ $\resultt\, T$, which are
either OK, an exception, or a break.
\begin{align*}
\ok    &{}: T \to \resultt\, T \coloneqq \lambda x\, o\, e\, b. o\, x \\
\err   &{}: \valt \to \resultt\, T \coloneqq \lambda x\, o\, e\, b. e\, x \\
\breakf&{}: \mathbb N \to \resultt\, T \coloneqq \lambda x\, o\, e\, b. b\, x
\end{align*}

A _value-path_ $\valpatht = (\valt,\, \optt\, \stream \valt)$ is
a pair of a value and an optional list of values.
The optional list is called the _path_ of the value.
The idea behind it is that if the path is present,
it represents the location of the value in input data.

We assume the existence of a set of Y combinators $Y_n$ that we will use to
define recursive functions of arity $n$.
For each $n$, we have that $Y_n f = f (Y_n f)$ holds.
Furthermore, the types of $Y_n$ are:
\begin{alignat*}{4}
Y_1:{}& ((T_1                 &&\to U) \to T_1                 &&\to U) \to T_1                 &&\to U \\
... \\
Y_n:{}& ((T_1 \to ... \to T_n &&\to U) \to T_1 \to ... \to T_n &&\to U) \to T_1 \to ... \to T_n &&\to U
\end{alignat*}
For example, these combinators allow us to define the concatenation of two lists $l$ and $r$ as
$$l + r \coloneqq Y_1\, (\lambda f\, l. l\, (\lambda h\, t. \cons\, h\, (f\, t))\, r)\, l,$$
which satisfies the property
$$l + r = l\, (\lambda h\, t. \cons\, h\, (t + r))\, r.$$
For simplicity, we will define recursive functions from here on mostly by equational properties,
from which we could easily derive proper definitions using the $Y_n$ combinators.

We define three monadic bind operators to describe composition.
For a result $r$ and a function $f$ from a value to a result,
$l \bindr f$ applies $f$ to $r$ if it is OK, else returns $r$ unchanged.
For a list $l$ and a function $f$ from a _value result_ to a list,
$l \bindl f$ applies $f$ to all elements of $l$ and concatenates the outputs.
For a list $l$ and a function $f$ from a _value_ to a list,
$l \bind f$ applies OK values in $l$ to $f$ and returns exception values in $l$.
\begin{alignat*}{7}
&\bindr&&{}: \resultt\, T &&\to (T &&\to \resultt\, U&&) &&\to \resultt\, U &&\coloneqq \lambda r\, f. r\, (\lambda o. f\, o)\, (\lambda e. r)\, (\lambda b. r) \\
&\bindl&&{}: \stream T &&\to (T &&\to \stream U&&) &&\to \stream U &&\coloneqq \lambda l\, f. l\, (\lambda h\, t. f\, h + (t \bindl f))\, \nil \\
&\bind &&{}: \stream{\resultt\, T} &&\to (T &&\to \stream{\resultt\, U}&&) &&\to \stream{\resultt\, U} &&\coloneqq \lambda l\, f. l \bindl (\lambda x. x\, (\lambda o. f\, o)\, (\lambda e. \stream x)\, (\lambda b. \stream x))
\end{alignat*}

## Implicit conversion

\newcommand{\fromvp}{\operatorname{from\_vp}}
\newcommand{\tovp}{\operatorname{to\_vp}}

We frequently mix values and value-paths.
To avoid boilerplate, we assume that in contexts where
one of these types is expected, but
a value of the other type is given,
the value is implicitly converted to match the expected type.
A value can be converted to and from a value-path with the following functions:
\begin{align*}
\tovp   &{}: \valt \to \valpatht \coloneqq \lambda v. \pair\, v\, \none \\
\fromvp &{}: \valpatht \to \valt \coloneqq \snd
\end{align*}
This conversion can also take place inside results and lists, as shown by the next example.

::: {.example}
If we have a value-path $v_p: \valpatht$ and
apply it to a function that expects a $\valt$, then
$v_p$ is implicitly substituted by
$\fromvp \v_p$.

If we have a result $r: \resultt\, \valt$ and
apply it to a function that expects a $\valpatht$, then
$r$ is implicitly substituted by
$r \bindr (\lambda v. \ok\, (\tovp v))$.

If we have a list $l: \stream{\resultt\, \valt}$ and
apply it to a function that expects a $\stream{\resultt\, \valpatht}$, then
$l$ is implicitly substituted by
$l \bindl (\lambda r. \stream{r \bindr (\lambda v. \ok\, (\tovp v))})$.
:::

## Value operations {#sec:value-ops}

In this subsection, we specify the functions and operations
that a value type must implement.
Their concrete definitions for JSON values are given in @sec:json.

For the value type $\valt$, there must be a type of numbers and a type of strings, such that
for any number $n$, $n$ is a value, and
for any string $s$, $s$ is a value.
Furthermore, for any boolean $b$, $b$ is a value.
By convention, we will write
$v$ for values,
$n$ for numbers, and
$s$ for strings
in the remainder of this text.

The value type must provide arithmetic operations $\{+, -, \times, \div, \modulo\}$
such that every arithmetic operation $\arith$ returns a value result, i.e.
$\arith: \valt \to \valt \to \resultt\, \valt$.
That means that every arithmetic operation can fail.
Definitions of the arithmetic operators for JSON values are given in @sec:arithmetic.

The value type must also provide Boolean operations
$\{<, \leq, >, \geq, \iseq, \neq\}$, where
$l \iseq r$ returns whether $l$ equals $r$, and
$l \neq r$ returns its negation.
Each of these Boolean operations is of type $\valt \to \valt \to \valt$.
The order on JSON values is defined in @sec:json-order.

We assume the existence of several functions:

- $\arr_0: \valt$ yields an empty array.
- $\arr_1: \valt \to \valt$ constructs a singleton array from a value.
- $\objf_0: \valt$ yields an empty object.
- $\objf_1: \valt \to \valt \to \resultt\, \valt$ constructs a singleton object from a key and value.
  (It returns a value result instead of a value because it
  may fail in case that the provided value is not a valid key.)
- $\bool: \valt \to \boolt$ takes a value and returns a boolean.

We use $\arr_0$ and $\arr_1$ to define a convenience function $\arr$
that transforms a list into a value result:
It returns an array if all list elements are values, or into
the first exception in the list otherwise:
\begin{alignat*}{2}
\sumf&{}: \stream{\resultt\, \valt} \to \valt &&\to \resultt\, \valt \coloneqq \lambda l\, v. l\, (\lambda h\, t. h \bindr (\lambda o. (v + o \bindr \sumf\, t)))\, (\ok\, v) \\
\arr &{}: \stream{\resultt\, \valt} &&\to \resultt\, \valt \coloneqq \lambda l. \sumf\, (l \bind (\lambda v. \stream{\ok\, (\arr_1\, v)}))\, \arr_0
\end{alignat*}
Here, the function $\sumf$ takes a list $l$ and a zero value $n$ and
returns the sum of the zero value and the list elements if they are all OK,
otherwise it returns the first exception in the list.
This uses the addition operator $+: \valt \to \valt \to \resultt\, \valt$.

<!-- TODO: path part definition in syntax section, but used already here -->
Let $p$ a path part (as defined in @sec:syntax) containing values as indices.
We assume two operators:

- The _access operator_ $v[p]$ extracts values contained within $v$
  at positions given by $p$, yielding a list of value-path results $\stream{\resultt\, \valpatht}$.
  This operator will be used in @sec:semantics and
  is defined for JSON values in @sec:json-access.
- The _update operator_ $v[p]^? \update f$ replaces
  those elements $v' = v[p]$ in $v$ by
  the output of $f\, v'$, where $f: \valt \to \stream{\resultt\, \valt}$.
  The update operator yields a single value result.
  This operator will be used in @sec:updates and
  is defined for JSON values in @sec:json-update.

If $v[p]$ returns an error, then
$v[p] \update f$ should yield an error and
$v[p]? \update f$ should yield $v$.
We define $v[p]? = v[p] \bindl \lambda r. r\, (\lambda o. \stream r)\, (\lambda e. \stream{})\, (\lambda b. \stream r)$.
This simply discards any error yielded by $v[p]$.
