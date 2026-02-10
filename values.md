# Preliminaries {#sec:values}

In this section, we define several data types, such as
values, results, and lists, in simply typed lambda calculus.

## Basic data types

\newcommand{\some}{\operatorname{some}}
\newcommand{\none}{\operatorname{none}}
\newcommand{\fst}{\operatorname{fst}}
\newcommand{\snd}{\operatorname{snd}}

We use letters such as $T$ and $U$ for type variables.
Let us fix some standard encodings for
boolean values $\boolt$,
natural numbers $\mathbb N$,
optional values $\optt\, T$,
lists $\stream T$, and
pairs $(T, U)$:
$$
\begin{alignedat}{4}
\true &: \boolt &&\coloneqq \lambda t\, f. t \\
\false&: \boolt &&\coloneqq \lambda t\, f. f \\
\succf&: \mathbb N \to \mathbb N &&\coloneqq \lambda n\, s\, z. s\, n \\
\zero&: \mathbb N &&\coloneqq \lambda s\, z. z \\
\fst&{}: (T, U) \to T &&\coloneqq \lambda p. p\, (\lambda x\, y. x) \\
\snd&{}: (T, U) \to T &&\coloneqq \lambda p. p\, (\lambda x\, y. y)
\end{alignedat}
\qquad
\begin{alignedat}{4}
\some&: T \to \optt\,T &&\coloneqq \lambda x\, s\, n. s\, x \\
\none&: \optt\,T &&\coloneqq \lambda s\, n. n \\
\cons&: T \to \stream T \to \stream T &&\coloneqq \lambda h\, t. \lambda c\, n. c\, h\, t \\
\nil&: \stream T &&\coloneqq \lambda c\, n. n \\
\pair&{}: T \to U \to (T, U) &&\coloneqq \lambda x\, y\, p. p\, x\, y \\
\quad
\end{alignedat}
$$
We write the empty list
$\nil$ as $\stream{}$ and
$\cons\, r_1\, (\cons\, r_2\, ...)$ as $\stream{r_1, r_2, ...}$.
Because the jq language is evaluated lazily, lists can be infinite.

We assume a combinator $Y: (T \to T) \to T$ for which
$Y\, f = f\, (Y\, f)$ holds.
We will use this to define recursive functions;
for example, the concatenation of two lists $l$ and $r$ is
$$l + r \coloneqq Y\, (\lambda f\, l. l\, (\lambda h\, t. \cons\, h\, (f\, t))\, r)\, l,$$
which satisfies the property
$$l + r = l\, (\lambda h\, t. \cons\, h\, (t + r))\, r.$$
For simplicity, we will define recursive functions from here on mostly by equational properties,
from which we could easily derive proper definitions using the $Y$ combinator.

## Values {#sec:value-ops}

While jq operates uniquely on JSON values,
we define the jq semantics for a general value type $\valt$.
Let us start by defining a few types related to values.

A _result_ $\resultt\, T$ is either OK, an error, or a break.
Non-OK results are also called _exceptions_.
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

We now specify conditions for $\valt$.
Concrete definitions for JSON values are given in @sec:json.

For the value type $\valt$, there must be a type of numbers and a type of strings, such that
for any number $n$, $n$ is a value, and
for any string $s$, $s$ is a value.
Furthermore, for any boolean $b$, $b$ is a value.
By convention, we write
$v$ for values,
$n$ for numbers, and
$s$ for strings
in the remainder.
We write $l \coloneqq \quad r_1 \gror \dots \gror r_n$ to say that
$l$ is of shape $r_i$ for some $i \leq n$.

The value type must provide arithmetic operations
$\{+, -, \times, \div, \modulo\}$
of type $\valt \to \valt \to \resultt\, \valt$.
That means that every arithmetic operation can fail.
The value type must also provide Boolean operations
$\{<, \leq, >, \geq, \iseq, \neq\}$
of type $\valt \to \valt \to \valt$.
Here,
$l \iseq r$ returns whether $l$ equals $r$, and
$l \neq r$ returns its negation.

We assume the existence of several functions:

- $\arr: \stream{\resultt\, \valt} \to \resultt\, \valt$ yields an array result from a list of value results.
- $\objf_0: \valt$ yields an empty object.
- $\objf_1: \valt \to \valt \to \resultt\, \valt$ constructs a singleton object from a key and value.
  (It returns a value result instead of a value because it
  may fail in case that the provided value is not a valid key.)
- $\bool: \valt \to \boolt$ takes a value and returns a boolean.

A _position_ $p$ is defined by the grammar $p \coloneqq \quad \emptyset \gror v \gror v: \gror :v \gror v:v$.
The values contained in a position are called _indices_.
We assume two operators:

- The _access operator_ $v[p]$ extracts values contained within the value-path $v$
  at position $p$, yielding a list of value-path results $\stream{\resultt\, \valpatht}$.
  This operator will be used in @sec:semantics.
- The _update operator_[^update-op] $v[p] \update f$ replaces
  those elements $v' = v[p]$ in the value $v$ by
  the output of $f\, v'$, where $f: \valt \to \stream{\resultt\, \valt}$.
  The update operator yields a single value result
  $\resultt\, \valt$.
  This operator will be used in @sec:updates.

[^update-op]:
  Although jq's update operator "`|=`" resembles the semantic entailment relation "$\models$",
  it has a completely different meaning, deriving from
  the combination of composition "`|`" and update "`=`".
  We do not use semantic entailment "$\models$" in this paper.

We write $[]$ instead of $[\emptyset]$ and
define error-suppressing variants of these operators:
If $v[p]$ yields an error, then
$v[p]?$ yields $\stream{}$ and
$v[p]? \update f$ yields $\ok\, v$.
Otherwise, $v[p]? = v[p]$ and $(v[p]? \update f) = (v[p] \update f)$.

## Composition

We define three monadic bind operators to describe composition.
\begin{alignat*}{7}
&\bindr&&{}: \resultt\, T &&\to (T &&\to \resultt\, U&&) &&\to \resultt\, U &&\coloneqq \lambda r\, f. r\, (\lambda o. f\, o)\, (\lambda e. r)\, (\lambda b. r) \\
&\bindl&&{}: \stream T &&\to (T &&\to \stream U&&) &&\to \stream U &&\coloneqq \lambda l\, f. l\, (\lambda h\, t. f\, h + (t \bindl f))\, \nil \\
&\bind &&{}: \stream{\resultt\, T} &&\to (T &&\to \stream{\resultt\, U}&&) &&\to \stream{\resultt\, U} &&\coloneqq \lambda l\, f. l \bindl (\lambda x. x\, (\lambda o. f\, o)\, (\lambda e. \stream x)\, (\lambda b. \stream x))
\end{alignat*}

## Implicit conversion {#sec:implicit-conversion}

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
$\fromvp\, \v_p$.

If we have a result $r: \resultt\, \valt$ and
apply it to a function that expects a $\resultt\, \valpatht$, then
$r$ is implicitly substituted by
$r \bindr (\lambda v. \ok\, (\tovp\, v))$.

If we have a list $l: \stream{\resultt\, \valt}$ and
apply it to a function that expects a $\stream{\resultt\, \valpatht}$, then
$l$ is implicitly substituted by
$l \bindl (\lambda r. \stream{r \bindr (\lambda v. \ok\, (\tovp\, v))})$.
:::

## JSON values {#sec:json}

A JSON value $v$ has the shape
$$v \coloneqq \nullf \gror \false \gror \true \gror n \gror s \gror [v_0, ..., v_n] \gror \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n},$$
where $n$ is a number and $s$ is a string.
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
In JSON, object keys are strings.

We write $\err\, ...$ to denote $\err\, e$ where we do not want to specify $e$.
(In actual jq implementations, $e$ is frequently an error message string.)

The functions to construct arrays and objects, as well as to retrieve the _boolean value_, are as follows:
\begin{alignat*}{3}
& \arr  &:{}& \stream{\resultt\, \valt} \to \resultt\, \valt && \coloneqq \lambda l. \sumf\, (l \bind (\lambda v. \stream{\ok\, [v])}))\, [] \\
& \objf_0&:{}& \valt && \coloneqq \obj{} \\
& \objf_1&:{}& \valt \to \valt \to \resultt\, \valt && \coloneqq \lambda k\, v. \begin{cases}
  \ok \obj{k \mapsto v} & \text{if $k$ is a string} \\
  \err ... & \text{otherwise}
\end{cases} \\
& \bool&:{}& \valt \to \boolt && \coloneqq \lambda v. \begin{cases}
  \false & \text{if $v = \nullf$ or $v = \false$} \\
  \true & \text{otherwise}
\end{cases}
\end{alignat*}
The function "$\arr$" transforms a list of value results into a single value result:
It returns an array if all list elements are values, and
the first exception in the list otherwise.
It uses a helper function $\sumf$ that takes a list $l$ and an accumulator $v$.
It returns the sum of the accumulator and the list elements if they are all OK,
otherwise it returns the first exception in the list.
This uses the addition operator $+: \valt \to \valt \to \resultt\, \valt$.
$$\sumf: \stream{\resultt\, \valt} \to \valt \to \resultt\, \valt \coloneqq \lambda l\, v. l\, (\lambda h\, t. h \bindr (\lambda o. (v + o \bindr \sumf\, t)))\, (\ok\, v)$$

We are now going to define
the access operators $v[p]$ and
the update operators $v[p] \update f$.
For all these operators, it holds that
if $v$ is a boolean or a number,
then the operator yields an error.
Given that the definition of these operators
differs greatly between different jq implementations,
we are only going to cover a few basic cases for these operators
that all jq implementations agree on.
We omit all remaining cases, such as
indexing with non-integer numbers,
indexing with non-existing keys, and
slicing ($v[l:h]$).

\newcommand{\appvp}{\operatorname{app\_vp}}
The access operator $v[p]$ of a value-path $v$ at position $p$ is defined as follows:
$$v[] \coloneqq \begin{cases}
  \sum_i v[i] & \text{if $\fst v = [v_0, ..., v_n]$} \\
  \sum_i v[k_i] & \text{if $\fst v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$}
\end{cases}$$
$$v[i] \coloneqq \begin{cases}
  \stream{\ok\, (\appvp\, v\, v_i\, i)} & \text{if $\fst v = [v_0, ..., v_n]$, $i \in \mathbb N$, and $i \leq n$} \\
  \stream{\ok\, (\appvp\, v\, v_j\, i)} & \text{if $\fst v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$ and $k_j = i$}
\end{cases}$$
Here, we use $\sum_i v[i]$ to abbreviate $v[0] + \dots + v[n]$.
If there are no elements $i$ to iterate over
(i.e. because the input value is an empty array or object),
the sum returns the empty list $\stream{}$.
Furthermore, we use a helper function $\appvp$ that
takes a value-path $v_p$,
replaces its value by $v$, and
appends $i$ to its path if present:
$$\appvp: \valpatht \to \valt \to \valt \to \valpatht \coloneqq \lambda v_p\, v\, i.
\pair\, v\, (\snd\, v_p\, (\lambda p. \some\, (p + \stream i))\, \none)$$

The update operator $v[p] \update f$ is defined as follows:
$$v[] \update f \coloneqq \begin{cases}
  \arr\, (\sum_i (f\, v_i))
  & \text{if } v = [v_0, ..., v_n] \\
  \sumf (\sum_i \stream{\objf_?\, k_i\, (f\, v_i)}) \objf_0
  & \text{if $v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n}$}
\end{cases}$$
$$v[i] \update f \coloneqq \begin{cases}
  \begin{alignedat}{3}
  \arr\, (&\textstyle\sum_{j=0}^{i-1}&&\stream{\ok\, v_j} + (f\, v_i\, (\lambda h\, t. \stream{h})\, \stream{}) \\
  +{} &\textstyle\sum_{j=i+1}^n&&\stream{\ok\, v_j})
  \end{alignedat}
  &
  \begin{aligned}
  & \text{if $v = [v_0, ..., v_n]$, $i \in \mathbb N$,} \\
  & \quad \text{and } i \leq n
  \end{aligned}
  \\
  \begin{alignedat}{3}
  \sumf (&\textstyle\sum_{j=0}^{i-1}&&\stream{\objf_1\, k_j\, v_j} + \stream{\objf_?\, k\, (f\, v_i)} \\
  +{} &\textstyle\sum_{j=i+1}^n &&\stream{\objf_1\, k_j\, v_j}) \objf_0
  \end{alignedat}
  &
  \begin{aligned}
  & \text{if } v = \obj{k_0 \mapsto v_0, ..., k_n \mapsto v_n} \\
  & \quad \text{and } k_j = i
  \end{aligned}
\end{cases}$$
Here, we use a helper function for the case that $v$ is an object.
This function attempts to construct an object from
a key and (the first element of) a list:
$$\objf_?: \valt \to \stream{\resultt \valt} \to \resultt \valt \coloneqq \lambda k\, l. l\, (\lambda h\, t. h \bindr \lambda o. \objf_1\, k\, o)\, (\ok \objf_0)$$

::: {.example}
Let $v = \pair\, [1, 2]\, \none$, i.e. a value-path of an array without a path.
That means that we do not know where the value comes from.
Then we have that
$v[0] = \stream{\ok\, (\pair\, 1\, \none)}$,
$v[1] = \stream{\ok\, (\pair\, 2\, \none)}$, and
$v[] = v[0] + v[1]$.

We can update the value e.g. with $f \coloneqq \lambda x. \stream{x + 1}$.
Then we have that
$v[0] \update f = \ok\, [2, 2]$,
$v[1] \update f = \ok\, [1, 3]$, and
$v[] \update f = \ok\, [2, 3]$.
Note that here, implicit conversion (@sec:implicit-conversion)
casts the value-path $v$ to a value, allowing us to perform the update.
:::

::: {.example}
Let $v = \pair\, \obj{\jqstr{a} \mapsto [1, 2]}\, (\some\, \stream{})$,
i.e. a value-path with an empty path.
We have that
$v[\jqstr{a}] = \stream{\ok\, v'}$, where
$v' = \pair\, [1, 2]\, (\some\, \stream{\jqstr{a}})$.
This value-path $v'$ records where its value $[1, 2]$ came from, namely from $\jqstr{a}$.

Accessing $v'$ appends to its path, i.e.
$v'[0] = \stream{\ok\, (\pair\, 1\, (\some\, \stream{\jqstr{a}, 0}))}$.
:::
