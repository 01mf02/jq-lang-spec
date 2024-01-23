---
title: Formal specification of the jq language
author: Michael Färber
---

This section describes syntax and semantics for a subset of the jq language.
To set the formal syntax and semantics apart from
the concrete syntax introduced in [](#preliminaries),
we use cursive font (as in "$f$", "$v$") for the specification
instead of the previously used typewriter font (as in "`f`", "`v`").


## Syntax

A *filter* $f$ is defined by
$$f \coloneqq n \mid \$x \mid . \mid .[] \mid .[f] \mid [f] \mid (f) \mid f? \mid f \star f \mid f \circ f \mid \ifj f \thenj f \elsej f \mid x \mid x(f; \dots; f)$$
where $n$ is an integer and $x$ is an identifier (such as "empty").
We call $\$x$ a variable.
By convention, we write $\$x'$ to denote a fresh variable.
The potential instances of $\star$ and $\circ$ are given in [](#tab:binops).
Furthermore, $f$ can be
a variable binding of the shape "$f \as \$x \mid f$" or
a fold of the shape "$\phi\; f \as \$x (f; f)$", where $\phi$ is either "reduce" or "foreach".

Table: Binary operators, given in order of increasing precedence.
  Operators surrounded by parentheses have equal precedence.\label{tab:binops}

Name      | Symbol  | Operators
--------- | ------- | ---------
Complex   | $\star$ | "$\mid$", ",", "$\models$", "or", "and"
Cartesian | $\circ$ | ($=$, $\neq$), ($<$, $\leq$, $>$, $\geq$), ($+$, $-$), ($*$, $/$), $\%$

A *filter definition* has the shape
"$f(x_1; \dots; x_n) \coloneqq g$".
Here, $f$ is an $n$-ary filter where $g$ may refer to $x_i$.
For example, this allows us to define filters that produce the booleans,
by defining $\true \coloneqq (0 = 0)$ and $\false \coloneqq (0 \neq 0)$.

A value $v$ is defined by
$$v \coloneqq \true \mid \false \mid n \mid [v, \dots, v]$$
where $n$ is an integer.
While this captures only a subset of JSON values,
it provides a solid base to specify semantics such that
they are relatively straightforward to extend to the full set of JSON values.


## Semantics

The goals for creating these semantics were, in descending order of importance:

* Simplicity: The semantics should be easy to describe and implement.
* Performance: The semantics should allow for performant execution.
* Compatibility: The semantics should be consistent with jq.

Let us start with a few definitions.
A context is a mapping from variables to values.
A value result is either a value or an error $\bot$.
A stream of value results is written as $\langle v_0, \dots, v_n \rangle$.
The concatenation of two streams $s_1$, $s_2$ is written as $s_1 + s_2$.

The *evaluation* of a filter $f$ with a context $c$ and a value result $v$
is denoted as $f|^c_v$ and returns a stream of value results.
We impose for any filter $f$, $f|^c_\bot = \langle \bot \rangle$,
and define its evaluation semantics only on values.
We say that two filters $f, g$ are equivalent iff
$f|^c_v = g|^c_v$ for all $c$ and $v$.

We are now going to introduce a few helper functions.
The first function transform a stream into
an array if all stream elements are values, or into
the leftmost error[^leftmost] in the stream otherwise:
$$[\langle v_0, \dots, v_n\rangle] = \begin{cases}
\left[v_0, \dots, v_n\right] & \text{if for all  } i, v_i \neq \bot \\
v_{\min\{i \mid v_i = \bot\}} & \text{otherwise} \\
\end{cases}$$
The next function helps define filters such as if-then-else, conjunction, and disjunction:
$$\ite(v, i, t, e) = \begin{cases}
\langle \bot \rangle & \text{if } v = \bot \\
t & \text{if } v \neq \bot \text{ and } v = i \\
e & \text{otherwise}
\end{cases}$$
The last function serves to retrieve the $i$-th element from a list, if it exists:
$$v[i] = \begin{cases}
v_i & \text{if } v = [v_0, \dots, v_n] \text{ and } 0 \leq i < n \\
\bot & \text{otherwise}
\end{cases}$$

To evaluate calls to filters that have been introduced by definition,
we define the substitution $\varphi[f_1 / x_1, \dots, f_n / x_n]$ to be
$\sigma \varphi$, where
$\sigma = \left\{x_1 \mapsto f_1, \dots, x_n \mapsto f_n\right\}$.
The substitution $\sigma \varphi$ is defined in [](#tab:substitution):
It both applies the substitution $\sigma$ and
replaces all variables bound in $\varphi$ by fresh ones.
This prevents variable bindings in $\varphi$ from
shadowing variables that occur in the co-domain of $\sigma$.

Example
: Consider the filter "$0 \as \$x \mid f(\$x)$", where "$f(g) \coloneqq 1 \as \$x \mid g$".
  Here, "$f(\$x)$" expands to "$1 \as \$x' \mid \$x$", where "$\$x'$" is a fresh variable.
  The whole filter expands to "$0 \as \$x \mid 1 \as \$x' \mid \$x$",
  which evaluates to 0.
  If we would (erroneously) fail to replace $\$x$ in $f(g)$ by a fresh variable, then
  the whole filter would expand to "$0 \as \$x \mid 1 \as \$x \mid \$x$",
  which evaluates to 1.

[^leftmost]:
  In these simplified semantics, we have only a single kind of error, $\bot$,
  so it might seem pointless to specify which error we return.
  However, in an implementation, we may have different kinds of errors.

Table: Substitution. Here,
  $\$x'$ is a fresh variable and
  $\sigma' = \sigma\left\{\$x \mapsto \$x'\right\}$.
  \label{tab:substitution}

$\varphi$ | $\sigma\varphi$
--- | ---
$.$, $n$ (where $n \in \mathbb{Z}$), or $.[]$ | $\varphi$
$\$x$ or $x$ | $\sigma(\varphi)$
$.[f]$ | $.[\sigma f]$
$f?$ | $(\sigma f)?$
$f \star g$ | $\sigma f \star \sigma g$
$f \circ g$ | $\sigma f \circ \sigma g$
$\ifj f \thenj g \elsej h$ | $\ifj \sigma f \thenj \sigma g \elsej \sigma h$
$x(f_1; \dots; f_n)$ | $x(\sigma f_1; \dots; \sigma f_n)$
$f \as \$x \mid g$ | $\sigma f \as \$x' \mid \sigma' g$
$\phi\; xs \as \$x (init; f)$ | $\phi\; \sigma xs \as \$x'(\sigma init; \sigma' f)$

Table: Evaluation semantics. \label{tab:eval-semantics}

$\varphi$ | $\varphi|^c_v$
- | ----
$\emptys$ | $\langle \rangle$
$.$ | $\langle v \rangle$
$n$ (where $n \in \mathbb{Z}$) | $\langle n \rangle$
$\$x$ | $\langle c(\$x) \rangle$
$[f]$ | $\langle \left[f|^c_v\right] \rangle$
$f, g$ | $f|^c_v + g|^c_v$
$f \mid g$ | $\sum_{x \in f|^c_v} g|^c_x$
$f \as \$x \mid g$ | $\sum_{x \in f|^c_v} g|^{c\{\$x \mapsto x\}}_v$
$f \circ g$ | $\sum_{x \in f|^c_v} \sum_{y \in g|^c_v} \langle x \circ y \rangle$
$f?$ | $\sum_{x \in f|^c_v} \begin{cases}\langle \rangle & \text{if } x = \bot \\ \langle x \rangle & \text{otherwise}\end{cases}$
$f \andj g$ | $\sum_{x \in f|^c_v} \ite(x, \false, \langle \false \rangle, g|^c_v)$
$f \orj g$ | $\sum_{x \in f|^c_v} \ite(x, \true,  \langle \true \rangle, g|^c_v)$
$\ifj f \thenj g \elsej h$ | $\sum_{x \in f|^c_v} \ite(x, \true, g|^c_v, h|^c_v)$
$.[]$ | $\begin{cases}\langle v_0, \dots, v_n\rangle & \text{if } v = [v_0, \dots, v_n] \\ \langle \bot \rangle & \text{otherwise}\end{cases}$
$.[f]$ | $\sum_{i \in f|^c_v} \langle v[i] \rangle$
$\phi\; xs \as \$x (init; f)$ | $\sum_{i \in init|^c_v} \phi^c_i(xs|^c_v, f)$
$x(f_1; \dots; f_n)$ | $g[f_1 / x_1, \dots, f_n / x_n]|^c_v$ if $x(x_1; \dots; x_n) \coloneqq g$
$f \models g$ | see [](#tab:update-semantics)

The evaluation semantics are given in [](#tab:eval-semantics).
We suppose that the Cartesian operator $\circ$ is defined on pairs of values,
yielding a value result.
We have seen examples of the shown filters in [](#preliminaries).
The semantics diverge relatively little from the implementation in jq.
One notable exception is $f \circ g$, which jq evaluates differently as
$\sum_{y \in g|^c_v} \sum_{x \in f|^c_v} \langle x \circ y \rangle$.
The reason will be given in [](#cloning).
Note that the difference only shows when both $f$ and $g$ return multiple values.

$$\phi^c_v(xs, f) \coloneqq \begin{cases}
\langle \phantom{v} \rangle + \sum_{x \in f|^{c\{\$x \mapsto x\}}_v}\phi^c_x(xt, f) & \text{if } xs = \langle x \rangle + xt \text{ and } \phi = \reduce \\
\langle v \rangle + \sum_{x \in f|^{c\{\$x \mapsto x\}}_v}\phi^c_x(xt, f) & \text{if } xs = \langle x \rangle + xt \text{ and } \phi = \foreachj \\
\langle v \rangle & \text{otherwise}
\end{cases}$$

In addition to the filters defined in [](#tab:eval-semantics),
we define the semantics of the two fold-like filters "reduce" and "foreach" as follows,
where $xs$ evaluates to $\langle x_0, \dots, x_n \rangle$:
\begin{align*}
\reduce   xs \as \$x\; (init;\, f) &= init &
\foreachj xs \as \$x\; (init;\, f) &= init \\
& \mid x_0 \as \$x \mid f &
& \mid ., (x_0 \as \$x \mid f \\
& \mid \dots &
& \mid \dots \\
& \mid x_n \as \$x \mid f &
& \mid ., (x_n \as \$x \mid f)\dots) \\
\end{align*}
Both filters fold $f$ over the sequence $xs$ with the initial value $init$.
Their main difference is that "reduce" returns only the final value(s),
whereas "foreach" also returns all intermediate ones.

The following property can be used to eliminate bindings.

Lemma
: Let $\varphi(f)$ be a filter such that $\varphi(f)|^c_v$ has the shape
  "$\sum_{x \in f|^c_v} \dots$".
  Then $\varphi(f)$ is equivalent to "$f \as \$x \mid \varphi(\$x)$".

Proof
: We have to prove the statement for $\varphi(f)$ set to
  "$f \mid g$", "$f \as \$x \mid g$", "$f \circ g$", "$f?$",
  "$f \andj g$", "$f \orj g$", "$\ifj f \thenj g \elsej h$",
  "$.[f]$", and "$\phi\; xs \as \$x(f; g)$".
  Let us consider the filter $\varphi(f)$ to be $.[f]$.
  Then we show that $.[f]$ is equivalent to $f \as \$x \mid .[\$x]$:
  \begin{align*}
  (f \as \$x \mid .[\$x])|^c_v
  &= \sum_{x \in f|^c_v} .[\$x]|^{c\{\$x \mapsto x\}}_v \\
  &= \sum_{x \in f|^c_v} \sum_{i \in \$x|^{c\{\$x \mapsto x\}}_v} \langle v[i] \rangle \\
  &= \sum_{x \in f|^c_v} \sum_{i \in \langle x \rangle} \langle v[i] \rangle \\
  &= \sum_{x \in f|^c_v} \langle v[x] \rangle \\
  &= .[f]|^c_v
  \end{align*}
  The other cases for $\varphi(f)$ can be proved similarly.

The semantics of jq and those shown in [](#tab:eval-semantics)
differ most notably in the case of updates; that is, $f \models g$.
We are going to deal with this in the next subsection.


## Updates

jq's update mechanism works with *paths*.
A path is a sequence of indices $i_j$ that can be written as $.[i_1]\dots[i_n]$.
It refers to a value that can be retrieved by the filter "$.[i_1] \mid \dots \mid .[i_n]$".
Note that "$.$" is a valid path, referring to the input value.

The update operation "$f \models g$" attempts to
first obtain the paths of all values returned by $f$,
then for each path, it replaces the value at the path by $g$ applied to it.
Note that $f$ is not allowed to produce new values; it may only return paths.

Example
: Consider the input value $[[1, 2], [3, 4]]$.
  We can retrieve the arrays $[1, 2]$ and $[3, 4]$ from the input with the filter "$.[]$", and
  we can retrieve the numbers 1, 2, 3, 4 from the input with the filter "$.[] \mid .[]$".
  To replace each number with its successor, we run "$(.[] \mid .[]) \models .+1$",
  obtaining $[[2, 3], [4, 5]]$.
  Internally, in jq, this first builds the paths
  $.[0][0]$, $.[0][1]$, $.[1][0]$, $.[1][1]$,
  then updates the value at each of these paths with $g$.

There are several problems with this approach to updates:
One of these problems is that if $g$ returns no output,
the collected paths may point to values that do not exist any more.

Example ex:update
: Consider the input value $[1, 2, 2, 3]$ and the filter
  "$.[] \models g$", where $g$ is "$\ifj . = 2 \thenj \emptys \elsej .$",
  which we might suppose to delete all values equal to 2 from the input list.
  However, the output of jq is $[1, 2, 3]$.
  What happens here is perhaps unexpected,
  but consistent with the above explanation of jq's semantics:
  jq builds the paths $.[0]$, $.[1]$, $.[2]$, and $.[3]$.
  Next, it applies $g$ to all paths.
  Applying $g$ to $.[1]$ removes the first occurrence of the number 2 from the list,
  leaving the list $[1, 2, 3]$ and the paths $.[2]$, $.[3]$ to update.
  However, $.[2]$ now refers to the number 3, and $.[3]$ points beyond the list.

Even if this particular example can be executed correctly with a special case for
filters that do not return exactly one output,
there are more general examples which this approach treats in unexpected ways.

Example ex:update-comma
: Consider the input value $[[0]]$ and the filter
  "$(.[],\; .[][]) \models g$", where $g$ is "$\ifj . = [0] \thenj [1, 1] \elsej .+1$".
  Executing this filter in jq first builds the path
  $.[0]$ stemming from "$.[]$", then
  $.[0][0]$ stemming from "$.[][]$".
  Next, executing $g$ on the first path yields the intermediate result
  $[[1, 1]]$.
  Now, executing $g$ on the remaining path yields $[[2, 1]]$,
  instead of $[[2, 2]]$ as we might have expected.

The general problem here is that the execution of the filter $g$ changes the input value,
yet only the paths constructed from the initial input are considered.
This leads to
paths pointing to the wrong data,
paths pointing to non-existent data (both occurring in [@ex:update]), and
missing paths ([@ex:update-comma]).

I now show different semantics that avoid this problem,
by interleaving calls to $f$ and $g$.
By doing so, these semantics can abandon the idea of paths altogether.

The semantics use a helper function that takes an input array $v$ and
replaces its $i$-th element by the output of $\sigma$ applied to it:
$$(.[i] \models \sigma)|^c_v = \begin{cases}
[\langle v_0, \dots, v_{i-1} \rangle + \sigma|^c_{v_i} + \langle v_{i+1}, \dots, v_n \rangle] & \text{if } v = [v_0, \dots, v_n] \text{ and } 0 \leq i < n \\
\bot & \text{otherwise}
\end{cases}$$

<!-- μονοπάτι = path -->
<!-- συνάρτηση = function -->

Table: Update semantics. Here, $\$x'$ is a fresh variable. \label{tab:update-semantics}

$\mu$ | $\mu \models \sigma$
-- | ---
$\emptys$ | $.$
$.$ | $\sigma$
$f \mid g$ | $f \models (g \models \sigma)$
$f, g$ | $(f \models \sigma) \mid (g \models \sigma)$
$f \as \$x \mid g$ | $\reduce f \as \$x'\; (.;\; g[\$x' / \$x] \models \sigma)$
$\ifj f \thenj g \elsej h$ | $\reduce f \as \$x'\; (.;\; \ifj \$x' \thenj g \models \sigma \elsej h \models \sigma)$
$.[f]$ | $\reduce f \as \$x'\; (.;\; .[\$x'] \models \sigma)$
$.[]$ | $[.[] \mid \sigma]$
$x(f_1; \dots; f_n)$ | $g[f_1 / x_1, \dots, f_n / x_n] \models \sigma$ if $x(x_1; \dots; x_n) \coloneqq g$

The update semantics are given in [](#tab:update-semantics).
The case for $f \as \$x \mid g$ is slightly tricky:
Here, the intent is that $g$ has access to $\$x$, but $\sigma$ does not.
This is to ensure compatibility with jq's original semantics,
which execute $\mu$ and $\sigma$ independently,
so $\sigma$ should not be able to access variables bound in $\mu$.
In order to ensure that, we
replace $\$x$ by a fresh variable $\$x'$ and
substitute $\$x$ by $\$x'$ in $g$.

Example
: Consider the filter $0 \as \$x \mid (1 \as \$x \mid .[\$x]) \models \$x$.
  This updates the input array at index $1$.
  If the right-hand side of "$\models$"
  had access to variables bound on the right-hand side,
  then the array element would be replaced by $1$,
  because the variable binding $0 \as \$x$ would be shadowed by $1 \as \$x$.
  However, because we enforce that
  the right-hand side does not have access to variables bound on the right-hand side,
  the array element is replaced by $0$, which is the value originally bound to $\$x$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.

<!--
We can define the plain assignment filter "$f = g$" by
"$. \as \$x \mid f \models (\$x \mid g)$", where
$\$x$ may not occur free in $f$ or $g$.
The difference between "$f \models g$" and "$f = g$" is: where
"$f \models g$" replaces all values $v$ at positions $f$ by $g$ applied to $v$,
"$f = g$" replaces all values   at positions $f$ by $g$ applied to the *same* value,
namely the input value of "$f = g$".
-->

<!--
In summary, the given semantics are easier to define and to reason about,
while keeping compatibility with the original semantics in most use cases.
Furthermore, avoiding to construct paths also appears to
be more performant, as I will show in [](#evaluation).
-->
