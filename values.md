# Values {#sec:values}

In this section, we define several data types, such as
values, value results, and lists, in simply typed lambda calculus.
To ease the understanding, we will informally give type names to certain terms.

While jq operates uniquely on JSON values,
we define the jq semantics for a general value type $\mathcal V$.
This value type must satisfy several properties that will be given in @sec:value-ops.
Furthermore, we assume that $\mathcal V$ can be encoded in lambda calculus.

We encode boolean values as follows:
\begin{align*}
\true : \mathbb B &\coloneqq \lambda t\, f. t \\
\false: \mathbb B &\coloneqq \lambda t\, f. f
\end{align*}

We assume the existence of functions
$\succf: \mathbb N \to \mathbb N$ and
$\zero: \mathbb N$ to construct natural numbers, as well as a function
$\nateq: \mathbb N \to \mathbb N \to \mathbb B$ that returns
$\true$ if two natural numbers are equal, else $\false$.
We use natural numbers to store label identifiers.

The elements returned by our filters are _value results_ $\mathcal R$, which are
either OK or an exception (an error or a break).
\begin{align*}
\ok    &: \mathcal V \to \mathcal R \coloneqq \lambda x\, o\, e\, b. o\, x \\
\err   &: \mathcal V \to \mathcal R \coloneqq \lambda x\, o\, e\, b. e\, x \\
\breakf&:  \mathbb N \to \mathcal R \coloneqq \lambda x\, o\, e\, b. b\, x
\end{align*}

We will use _lists_ $\mathcal L$ of value results as return type of filters.
Because the jq language is evaluated lazily, lists can be infinite.
\begin{alignat*}{3}
\cons&: \mathcal R \to \mathcal L \to{} &&\mathcal L \coloneqq \lambda h\, t. && \lambda c\, n. c\, h\, t \\
\nil&:                                  &&\mathcal L \coloneqq                && \lambda c\, n. n
\end{alignat*}

We write the empty list
$\nil$ as $\stream{}$ and
$\cons\, r_1\, (\cons\, r_2\, ...)$ as $\stream{r_1, r_2, ...}$.

We assume the existence of a set of Y combinators $Y_n$ that we will use to
define recursive functions of arity $n$.
For each $n$, we have that $Y_n f = f (Y_n f)$ holds.
Furthermore, the types of $Y_n$ are:
\begin{alignat*}{4}
Y_1: & ((T_1                 &&\to U) \to T_1                 &&\to U) \to T_1                 &&\to U \\
... \\
Y_n: & ((T_1 \to ... \to T_n &&\to U) \to T_1 \to ... \to T_n &&\to U) \to T_1 \to ... \to T_n &&\to U
\end{alignat*}

We define the concatenation of two lists $l$ and $r$ as
$$l + r \coloneqq Y_1\, (\lambda f\, l. l\, (\lambda h\, t. \cons\, h\, (f\, t))\, r)\, l,$$
which satisfies the equational property
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
&\bindr&&: \mathcal R &&\to (\mathcal V &&\to \mathcal R&&) &&\to \mathcal R &&\coloneqq \lambda r\, f. r\, (\lambda o. f\, o)\, (\lambda e. r)\, (\lambda b. r) \\
&\bindl&&: \mathcal L &&\to (\mathcal R &&\to \mathcal L&&) &&\to \mathcal L &&\coloneqq \lambda l\, f. l\, (\lambda h\, t. f\, h + (t \bindl f))\, \nil \\
&\bind &&: \mathcal L &&\to (\mathcal V &&\to \mathcal L&&) &&\to \mathcal L &&\coloneqq \lambda l\, f. l \bindl (\lambda x. x\, (\lambda o. f\, o)\, (\lambda e. \stream x)\, (\lambda b. \stream x))
\end{alignat*}


## Value operations {#sec:value-ops}

In this subsection, we specify the functions and operations
that a value type must implement.
Their concrete definitions for JSON values are given in @sec:json.

For the value type $\mathcal V$, there must be a type of numbers and a type of strings, such that
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
$\arith: \mathcal V \to \mathcal V \to \mathcal R$.
That means that every arithmetic operation can fail.
Definitions of the arithmetic operators for JSON values are given in @sec:arithmetic.

The value type must also provide Boolean operations
$\{<, \leq, >, \geq, \stackrel{?}{=}, \neq\}$, where
$l \stackrel{?}{=} r$ returns whether $l$ equals $r$, and
$l \neq r$ returns its negation.
Each of these Boolean operations is of type $\mathcal V \to \mathcal V \to \mathcal V$.
The order on JSON values is defined in @sec:json-order.

We assume the existence of several functions:

- $\arr_0: \mathcal V$ yields an empty array.
- $\arr_1: \mathcal V \to \mathcal V$ constructs a singleton array from a value.
- $\objf_0: \mathcal V$ yields an empty object.
- $\objf_1: \mathcal V \to \mathcal V \to \mathcal R$ constructs a singleton object from a key and value.
  (It returns a value result instead of a value because it
  may fail in case that the provided value is not a valid key.)
- $\bool: \mathcal V \to \mathbb B$ takes a value and returns a boolean.

We use $\arr_0$ and $\arr_1$ to define a convenience function $\arr$
that transforms a list into a value result:
It returns an array if all list elements are values, or into
the first exception in the list otherwise:
\begin{alignat*}{2}
\sumf&: \mathcal L \to \mathcal V &&\to \mathcal R \coloneqq \lambda l\, n. l\, (\lambda h\, t. h \bindr (\lambda o. (n + o \bindr \sumf\, t)))\, (\ok(n)) \\
\arr &: \mathcal L                &&\to \mathcal R \coloneqq \lambda l. \sumf\, (l \bind (\lambda v. \stream{\ok((\arr_1\, v))}))\, \arr_0
\end{alignat*}
Here, the function $\sumf$ takes a list $l$ and a zero value $n$ and
returns the sum of the zero value and the list elements if they are all OK,
otherwise it returns the first exception in the list.
This uses the addition operator $+: \mathcal V \to \mathcal V \to \mathcal R$.

Let $p$ a path part (as defined in @sec:syntax) containing values as indices.
We assume two operators:

- The _access operator_ $v[p]$ extracts values contained within $v$
  at positions given by $p$, yielding a list of value results.
  This operator will be used in @sec:semantics and
  is defined for JSON values in @sec:json-access.
- The _update operator_ $v[p]^? \update f$ replaces
  those elements $v' = v[p]$ in $v$ by
  the output of $f\, v'$, where $f: \mathcal V \to \mathcal L$.
  The update operator yields a single value result.
  This operator will be used in @sec:updates and
  is defined for JSON values in @sec:json-update.

If $v[p]$ returns an error, then
$v[p] \update f$ should yield an error and
$v[p]? \update f$ should yield $v$.
We define $v[p]? = v[p] \bindl \lambda r. r\, (\lambda o. \stream r)\, (\lambda e. \stream{})\, (\lambda b. \stream r)$.
This simply discards any error yielded by $v[p]$.
