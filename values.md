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

While `jq` operates uniquely on JSON values,
we define jq semantics for a general value type $\valt$.
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

The value type must provide the binary arithmetic operations
$\{+, -, \times, \div, \modulo\}$
of type $\valt \to \valt \to \resultt\, \valt$, as well as
a unary negation operation "$-$" of type $\valt \to \resultt\, \valt$.
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

We define three monadic bind operators to describe composition:
\begin{alignat*}{7}
&\bindr&&{}: \resultt\, T &&\to (T &&\to \resultt\, U&&) &&\to \resultt\, U &&\coloneqq \lambda r\, f. r\, (\lambda o. f\, o)\, (\lambda e. r)\, (\lambda b. r) \\
&\bindl&&{}: \stream T &&\to (T &&\to \stream U&&) &&\to \stream U &&\coloneqq \lambda l\, f. l\, (\lambda h\, t. f\, h + (t \bindl f))\, \nil \\
&\bind &&{}: \stream{\resultt\, T} &&\to (T &&\to \stream{\resultt\, U}&&) &&\to \stream{\resultt\, U} &&\coloneqq \lambda l\, f. l \bindl (\lambda x. x\, (\lambda o. f\, o)\, (\lambda e. \stream x)\, (\lambda b. \stream x))
\end{alignat*}
We also define two standard map functions over results and lists:
\begin{alignat*}{5}
&\mapr&&{}: (T \to U) &&\to \resultt\, T &&\to \resultt\, U &&\coloneqq \lambda f\, r. r \bindr (\lambda o. \ok\, (f\, o)) \\
&\mapl&&{}: (T \to U) &&\to \stream{T} &&\to \stream{U} &&\coloneqq \lambda f\, l. l \bindl (\lambda x. \stream{f\, x})
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
This conversion can also take place inside results and lists. For example:

- If we have a value-path $v_p: \valpatht$ and
  apply it to a function that expects a $\valt$, then
  $v_p$ is implicitly substituted by
  "$\fromvp\, \v_p$".
- If we have a result $r: \resultt\, \valt$ and
  apply it to a function that expects a $\resultt\, \valpatht$, then
  $r$ is implicitly substituted by
  "$\mapr\, \tovp\, r$".
- If we have a list $l: \stream{\resultt\, \valt}$ and
  apply it to a function that expects a $\stream{\resultt\, \valpatht}$, then
  $l$ is implicitly substituted by
  "$\mapl\, (\mapr\, \tovp)\, l$".
