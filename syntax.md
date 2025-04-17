# Syntax {#sec:syntax}

This section describes the syntax for a subset of the jq language
that will be used later to define the semantics in @semantics.
To set the formal syntax apart from
the concrete syntax introduced in @tour,
we use cursive font (as in "$f$", "$v$") for the specification
instead of the previously used typewriter font (as in "`f`", "`v`").

We will start by introducing high-level intermediate representation (HIR) syntax in @hir.
This syntax is very close to actual jq syntax.
Then, we will identify a subset of HIR as mid-level intermediate representation (MIR) in @mir
and provide a way to translate from HIR to MIR.
This will simplify our semantics in @semantics.
Finally, in @jq-syntax, we will show how HIR relates to actual jq syntax.

## HIR {#sec:hir}

A _filter_ $f$ is defined by the grammar
\begin{align*}
f &\coloneqq \quad n \gror s \gror . \gror .. \\
  &\gror (f) \gror f? \gror [] \gror [f] \gror \{f: f, ..., f: f\} \gror f [p]^? ... [p]^? \\
  &\gror f \star f \gror f \cartesian f \\
  &\gror f \as P | f \gror \reduce f \as P\; (f; f) \gror \foreach f \as P\; (f; f; f) \gror \$x \\
  &\gror \labelx x | f \gror \breakx x \\
  &\gror \ite{f}{f}{f} \gror \try f \gror \try f \catch f \\
  &\gror \deff x\!: f;\; f \gror \deff x(x; ...; x)\!: f;\; f \\
  &\gror x \gror x(f; ...; f)
\end{align*}
where:

- $p$ is a _path part_ defined by the grammar $p \coloneqq \quad \emptyset \gror f \gror f: \gror :f \gror f:f$.
- $P$ is a _pattern_ defined by the grammar $P \coloneqq \quad \$x \gror [P, ..., P] \gror \{f: P, ..., f: P\}$.
- $x$ is an identifier (such as "empty").
- $n$ is a number (such as $42$ or $3.14$).
- $s$ is a string (such as "Hello world!").

We use the superscript "$?$" to denote an optional presence of "?"; in particular,
$f [p]^?... [p]^?$ can be
$f [p]$, $f [p]?$,
$f [p] [p]$, $f [p]? [p]$, $f [p] [p]?$, $f [p]? [p]?$,
$f [p] [p] [p]$, and so on.
We write $[]$ instead of $[\emptyset]$.
The potential instances of the operators $\star$ and $\cartesian$ are given in @tab:binops.
All operators $\star$ and $\cartesian$ are left-associative, except for
"$|$", "$=$", "$\update$", and "$\aritheq$".

We will handle the operators "reduce" and "foreach" very similarly; therefore,
we introduce $\fold$ to stand for either "reduce" or "foreach".
However, because "reduce" takes one argument less than "foreach",
we simply ignore the superfluous argument when handling "reduce".

| Name | Symbol | Operators |
| ---- | ------ | --------- |
| Complex | $\star$ | "$|$", ",", ("=", "$\update$", "$\aritheq$", "$\alteq$"), "$\alt$", "or", "and" |
| Cartesian | $\cartesian$ | ($\overset{?}{=}$, $\neq$), ($<$, $<=$, $>$, $>=$), $\arith$ |
| Arithmetic | $\arith$ | ($+$, $-$), ($\times$, $\div$), $\%$

Table:
  Binary operators, given in order of increasing precedence.
  Operators surrounded by parentheses have equal precedence.
  {#tab:binops}

We consider equivalent the following notations:

- $f?$ and $\try f$,
- $x()$ and $x$,
- $\foreach f_x \as P (f_y; f)$ and $\foreach f_x \as P (f_y; f; .)$,
- $\deff x(): f; g$ and
  $\deff x: f; g$.


## MIR {#sec:mir}

We are now going to identify a subset of HIR called MIR and
show how to _lower_ a HIR filter to a semantically equivalent MIR filter.
This allows us later to define semantics for MIR in a much less verbose way than for HIR.

A MIR filter $f$ is defined by the grammar
\begin{align*}
f \coloneqq& \quad n \gror s \gror . \\
  \gror& [] \gror [f] \gror {} \gror \{\$x: \$x\} \gror .[p] \\
  \gror& f \star f \gror \$x \cartesian \$x \\
  \gror& f \as \$x | f \gror \reduce f \as \$x (.; f) \gror \foreach f \as \$x (.; f; f) \gror \$x \\
  \gror& \ite{\$x}{f}{f} \gror \try f \catch f \\
  \gror& \labelx x | f \gror \breakx x \\
  \gror& \deff x(x; ...; x): f; f \\
  \gror& x(f; ...; f)
\end{align*}
where $p$ is a path part containing variables instead of filters as indices.
Furthermore, the set of complex operators $\star$ in MIR
does not include "$=$" and "$\aritheq$" anymore.

Compared to HIR, MIR filters
have significantly simpler path operations
($.[p]$ versus $f [p]^?... [p]^?$) and
replace certain occurrences of filters by variables
(e.g. $\$x \cartesian \$x$ versus $f \cartesian f$).

| $\varphi$ | $\floor \varphi$ |
| ----- | ------------ |
| $n$, $s$, $.$, $\$x$, or $\breakx x$ | $\varphi$ |
| $..$ | $\deff \recurse: ., (.[]? | recurse); recurse$ |
| $(f)$ | $\floor f$ |
| $f?$ | $\labelx{x'} | \try \floor f \catch (\breakx{x'})$ |
| $[]$ or $\{\}$ | $\varphi$ |
| $[f]$ | $[\floor f]$ |
| $\{f: g\}$ | $\floor f \as \$x' | \floor g \as \$y' | \{\$x': \$y'\}$ |
| $\{f_1: g_1, \dots, f_n: g_n\}$ | $\floor{\{f_1: g_1\} + ... + \{f_n: g_n\}}$ |
| $f [p_1]^? \dots [p_n]^?$ | $. \as \$x' | \floor f | \floor{[p_1]^?}_{\$x'} | ... | \floor{[p_n]^?}_{\$x'}$ |
| $f = g$ | $\floor g \as \$x' | \floor{f \update \$x'}$ |
| $f \aritheq g$ | $\floor g \as \$x' | \floor{f \update . \arith \$x'}$ |
| $f \alteq g$ | $\floor{f \update . \alt g}$ |
| $f \andop g$ | $\floor{\ite{f}{(g | \bool)}{\text{false}}}$ |
| $f \orop g$ | $\floor{\ite{f}{\text{true}}{(g | \bool)}}$ |
| $f \star g$ | $\floor f \star \floor g$ |
| $f \cartesian g$ | $\floor f \as \$x' | \floor g \as \$y' | \$x' \cartesian \$y'$ |
| $f \as \$x | g$ | $\floor f \as \$x | \floor g$ |
| $f \as P | g$ | $\floor f \as \$x' | \floor{\$x' \as P | g}$,
| $\$x \as [P_1, ..., P_n] | g$ | $\floor{\$x \as {(0): P_1, ..., (n-1): P_n} | g}$ |
| $\$x \as {f_1: P_1, ...} | g$ | $\floor{.[\$x | f_1] \as \$x' | \$x' \as P_1 | \$x \as {f_2: P_2, ...} | g}$ |
| $\$x \as \{\} | g$ | $\floor g$ |
| $\fold f_x \as \$x (f_y; f; g)$ | $. \as \$x' | \floor{f_y} | \fold \floor{\$x'} | f_x) \as \$x (.; \floor f; \floor g)$ |
| $\fold f_x \as P (f_y; f; g)$ | $\floor{\fold (f_x \as P | \beta P) \as \$x' (f_y; \$x' \as \beta P | f; \$x' \as \beta P | g)}$ |
| $\ite{f_x}{f}{g}$ | $\floor{f_x} \as \$x' | \ite{\$x'}{\floor f}{\floor g}$ |
| $\try f \catch g$ | $\labelx{x'} | \try \floor f \catch {\floor g, \breakx{x'}}$ |
| $\labelx x | f$ | $\labelx x | \floor f$ |
| $\deff x: f; g$ | $\deff x: \floor f; \floor g$ |
| $\deff x(x_1; ...; x_n): f; g$ | $\deff x(x_1; ...; x_n): \floor f; \floor g$ |
| $x(f_1; ...; f_n)$ | $x(\floor{f_1}; ...; \floor{f_n})$ |

Table: Lowering of a HIR filter $\phi$ to a MIR filter $\floor \phi$. {#tab:lowering}

@tab:lowering shows how to lower an HIR filter $\varphi$ to
a semantically equivalent MIR filter $\floor \varphi$.
In particular, this desugars path operations and
makes it explicit which operations are Cartesian or complex.
By convention, we write $\$x'$ to denote a fresh variable.
Notice that for some complex operators $\star$, namely
"$=$", "$\aritheq$", "$\alteq$", "$\andop$", and "$\orop$",
@tab:lowering specifies individual lowerings, whereas
for the remaining complex operators $\star$, namely
"$|$", "$,$", "$\update$", and "$\alt$",
@tab:lowering specifies a uniform lowering $\floor{f \star g} = \floor f \star \floor g$.

<!--
The filter $ "empty" := ({} | .[]) \as \$x | . $ returns an empty stream.
We might be tempted to define it as ${} | .[]$,
which constructs an empty object, then returns its contained values,
which corresponds to an empty stream as well.
However, such a definition relies on the temporary construction of new values
(such as the empty object here),
which is not admissible on the left-hand side of updates (see @updates).
To ensure that $"empty"$ can be employed also as a path expression,
we define it in this complicated manner.
-->

We define filters that yield the boolean values as
\begin{align*}
"true"  &\coloneqq 0    = 0, \\
"false" &\coloneqq 0 \neq 0.
\end{align*}
The filter $\bool \coloneqq \ite{.}{\true}{\false}$
maps its input to its boolean value.

In the lowering of the folding operators $\fold f_x \as P (f_y; f; g)$
(where $\fold$ stands for either $\reduce$ or $\foreach$),
we replace the pattern $P$ by a variable by
"serialising" and "deserialising" the variables bound by $P$ with $\beta P$.
Here, $\beta P$ denotes the sequence of variables bound by $P$:
$$\beta P = \begin{cases}
  \sum_i \beta P_i & \text{if } P = [P_1, ..., P_n] \text{ or } P = \{f_1: P_1, \dots, f_n: P_n\} \\
  [\$x] & \text{if } P = \$x
\end{cases}$$
(We used $\sum_i x_i = x_1 + ... + x_n$ and $[x_1, ..., x_n] + [y_1, ..., y_m] = [x_1, ..., x_n, y_1, ..., y_m]$.)
In particular, we exploit the property that
$f \as P | g$ can be rewritten to
$$ f \as P | \beta P \as \$x' | \$x' \as \beta P | g, $$
because $\beta P$ can be interpreted both as pattern and as filter.

::: {.example}
  Consider the filter $\varphi \equiv f \as [\$x, [\$y], \$z] | g$.
  This filter destructures all outputs of $f$ that are of the shape
  $[x, [y, ...], z, ...]$ and binds the values
  $x$, $y$, and $z$ to the respective variables.
  Here, $\varphi$ uses the pattern
  $P = [\$x, [\$y], \$z]$ for which
  $\beta P = [\$x, \$y, \$z]$.
  It holds that $\varphi$ is equivalent to
  $$ f \as [\$x, [\$y], \$z]
  | [\$x, \$y, \$z] \as \$x'
  | \$x' \as [\$x, \$y, \$z] | g. $$
  Here, we first used $\beta P$ as filter
  ($[\$x, \$y, \$z] \as \$x' | ...$) to "serialise" the pattern variables to an array, then as pattern
  ($\$x' \as [\$x, \$y, \$z] | ...$) to "deserialise" the array to retrieve the pattern variables.
:::

| $[p]  ^?$ | $\floor{[p]^?}_{\$x}$ |
| --------- | ---------------------- |
| $[   ]^?$ | $.[]^?$,
| $[f  ]^?$ | $(\$x | \floor f) \as \$y' | .[\$y']^?$ |
| $[f: ]^?$ | $(\$x | \floor f) \as \$y' | .[\$y':]^?$ |
| $[ :f]^?$ | $(\$x | \floor f) \as \$y' | .[:\$y']^?$ |
| $[f:g]^?$ | $(\$x | \floor f) \as \$y' | (\$x | \floor g) \as \$z' | .[\$y':\$z']^?$ |

Table: Lowering of a path part $[p]^?$ with input $\$x$ to a MIR filter. {#tab:lower-path}

@tab:lower-path shows how to lower a path part $p^?$ to MIR filters.
Like in @sec:hir, the meaning of superscript "$?$" is an optional presence of "$?$".
In the lowering of $f [p_1]^? ... [p_n]^?$ in @tab:lowering,
if $[p_i]$ in the first column is directly followed by "?", then
$\floor{[p_i]^?}_{\$x}$ in the second column stands for
$\floor{[p_i] ?}_{\$x}$, otherwise for
$\floor{[p_i]  }_{\$x}$.
Similarly, in @tab:lower-path, if $[p]$ in the first column is followed by "$?$", then
all occurrences of superscript "?" in the second column stand for "?", otherwise for nothing.

::: {.example}
  The HIR filter $(.[]?[])$ is lowered to
  $(. \as \$x' | . | .[]? | .[])$.
  Semantically, we will see that this is equivalent to $(.[]? | .[])$.
:::

::: {.example}
  The HIR filter $\mu \equiv .[0]$ is lowered to
  $\floor \mu \equiv . \as \$x | . | (\$x | 0) \as \$y | .[\$y]$.
  Semantically, we will see that $\floor \mu$ is equivalent to $0 \as \$y | .[\$y]$.
  The HIR filter $\varphi \equiv [3] | .[0] = (\length, 2)$ is lowered to the MIR filter
  $\floor \varphi \equiv [3] | (\length, 2) \as \$z | \floor \mu \update \$z$.
  In @sec:semantics, we will see that its output is $\stream{[1], [2]}$.
:::

The lowering in @tab:lowering is compatible with the semantics of the jq implementation,
with one notable exception:
In jq, Cartesian operations $f \cartesian g$ would be lowered to
$\floor g \as \$y' | \floor f \as \$x' | \$x \cartesian \$y$, whereas we lower it to
$\floor f \as \$x' | \floor g \as \$y' | \$x \cartesian \$y$,
thus inverting the binding order.
Note that the difference only shows when both $f$ and $g$ return multiple values.
We diverge here from jq to make the lowering of Cartesian operations
consistent with that of other operators, such as $\{f: g\}$, where
the leftmost filter ($f$) is bound first and the rightmost filter ($g$) is bound last.
That also makes it easier to describe other filters, such as
$\{f_1: g_1, ..., f_n: g_n\}$, which we can lower to
$\floor{\{f_1: g_1\} + ... + \{f_n: g_n\}}$, whereas its lowering assuming the jq lowering of Cartesian operations would be
$$\floor{\{f_1: g_1\}} \as \$x'_1 | ... | \floor{\{f_n: g_n\}} \as \$x'_n | \$x'_1 + ... + \$x'_n.$$

::: {.example}
  The filter $(0, 2) + (0, 1)$ yields
  $\stream{0, 1, 2, 3}$ using our lowering, and
  $\stream{0, 2, 1, 3}$ in jq.
:::

Informally, we say that a filter is _wellformed_ if all references to
named filters, variables, and labels were previously bound.
For example, the filter $a + \$x$ is not wellformed because
neither $a$ nor $\$x$ was previously bound, but the filter
$\deff a: 1; 2 \as \$x | a + \$x$ is wellformed.
@tab:wf specifies in detail if a filter is wellformed.
For this, it uses a context $c = (d, v, l)$, consisting of
a set $d$ of pairs $(x, n)$ storing the name $x$ and the arity $n$ of a filter,
a set $v$ of variables, and
a set $l$ of labels.
We say that a filter $\varphi$ is wellformed with respect to a context $c$ if
$\wf(\varphi, c)$ is true.

| $\varphi$ | $\wf(\varphi, c)$ |
| --------- | ----------------- |
| $n$, $s$, $.$, $.[p]^?$, $\{\}$ | $\top$ |
| $\$x$ | $\$x \in v$ |
| $\breakx x$ | $\$x \in l$ |
| $[f]$ | $\wf(f, c)$ |
| $\{\$x: \$y\}$, $\$x \cartesian \$y$ | $\$x \in v \andop \$y \in v$,
| $f \star g$, $\try f \catch g$ | $\wf(f, c) \andop \wf(g, c)$ |
| $f \as \$x | g$ | $\wf(f) \andop \wf(g, (d, v \cup \{\$x\}, l))$ |
| $\labelx x | f$ | $\wf(f, (d, v, l \cup \{\$x\}))$ |
| $\ite{\$x}{f}{g}$ | $\$x \in v \andop \wf(f, c) \andop \wf(g, c)$ |
| $\fold f_x \as \$x (.; f; g)$ | $\wf(f_x, c) \andop \wf((f | g), (d, v \cup \{\$x\}, l))$ |
| $\deff x(x_1; \dots; x_n): f; g$ | $\wf(f, (d \cup \bigcup_i \{(x_i, 0)\}, v, l)) \andop \wf(g, (d \cup \{(x, n)\}, v, l))$ |
| $x(f_1; ...; f_n)$ | $(x, n) \in d \andop \forall i. \wf(f_i, c)$ |

Table: Wellformedness of a MIR filter $\varphi$ with respect to a context $c = (d, v, l)$. {#tab:wf}

For hygienic reasons, we require that labels are disjoint from variables.
This can be easily ensured by prefixing labels and variables differently.

::: {.example}
  Consider the filter $\labelx x | . \as \$x | \$x + \$x, \breakx x$.
  Here, we have to rename to ensure that labels and variables are disjoint, yielding e.g.
  $\labelx{l_x} | . \as \$v_x | \$v_x + \$v_x, \breakx{l_x}$.
:::

Furthermore, we require that identifiers with the same name represent filters with equal arity.
This can be ensured by postfixing all identifiers with their arity.

::: {.example}
  Consider the filter $\deff f(g): g; \deff f: .; f(f)$.
  Here, we have to rename identifiers to prevent shadowing issues in the semantics, yielding e.g.
  $\deff f^1(g^0): g^0; \deff f^0: .; f^1(f^0)$.
:::

## Concrete jq syntax {#sec:jq-syntax}

Let us now go a level above HIR, namely a subset of actual jq syntax^[
  Actual jq syntax has a few more constructions to offer, including
  variable arguments, string interpolation, modules, etc.
  However, these constructions can be transformed into
  semantically equivalent syntax as treated in this text.
] of which we have seen examples in @sec:tour, and
show how to transform jq filters to HIR and to MIR.

The syntax of filters in concrete jq syntax is nearly the same as in HIR.
To translate between the operators in @tab:binops, see @tab:op-correspondence.
The arithmetic update operators in jq, namely
`+=`,
`-=`,
`*=`,
`/=`, and
`%=`,
correspond to the operators $aritheq$ in HIR, namely
$\mathrel{+\!\!=}$,
$-\!\!=$,
$\times\!\!=$,
$\div\!\!=$, and
$\%\!\!=$.
Filters of the shape
`if f then g else h end` correspond to the filter
$\ite{f}{g}{h}$ in HIR;
that is, in HIR, the final `end` is omitted.
Filters of the shape
`if f1 then g1 elif f2 then g2 ... elif fn then gn else h end` are equivalent to
`if f1 then g1 else if f2 then g2 else ... if fn then gn else h end ... end end`.
Furthermore, in jq, it is invalid syntax to
call a nullary filter as `x()` instead of `x`, or to
define a nullary filter as `def x(): f; g` instead of `def x: f; g`.

--- --- --- --- --------- -------- ------ ----------------- ------ --- ------ --- ------ --- --- -------- ------ ----
jq  `|` `,` `=` `|=`      `//=`    `//`   `==`              `!=`   `<` `<=`   `>` `>=`   `+` `-` `*`      `/`    `%`
HIR $|$ $,$ $=$ $\update$ $\alteq$ $\alt$ $\stackrel{?}{=}$ $\neq$ $<$ $\leq$ $>$ $\geq$ $+$ $-$ $\times$ $\div$ $\%$
--- --- --- --- --------- -------- ------ ----------------- ------ --- ------ --- ------ --- --- -------- ------ ----

Table: Operators in concrete jq syntax and their corresponding HIR operators. {tab:op-correspondence}

To convert a jq filter `f` to MIR, we convert `f` to HIR, then to MIR, using @tab:lowering.

::: {.example}
  Consider the jq program `def recurse(f): ., (f | recurse(f)); recurse(. + 1)`,
  which returns the infinite stream of output values $n, n+1, \dots$
  when provided with an input number $n$.
  This example can be converted to the HIR filter
  $\deff \recurse(f): ., (f | \recurse(f)); \recurse(. + 1).$
  Lowering this to MIR yields
  $\deff \recurse(f): ., (f | \recurse(f)); \recurse(. \as \$x' | 1 \as \$y' | \$x' + \$y').$
:::

::: {.example}
  Consider the following jq program:

  ```
  def empty: {}[] as $x | .
  def select(f): if f then . else empty end;
  def negative: . < 0;
  .[] | select(negative)
  ```

  When given an array as an input, it yields
  those elements of the array that are smaller than $0$.
  This example can be converted to the HIR filter
  \begin{align*}
  &\deff \emptyf: \{\}[] \as \$x | .; \\
  &\deff \operatorname{select}(f): \ite{f}{.}{\emptyf}; \\
  &\deff \operatorname{negative}: . < 0; \\
  &.[] | \operatorname{select}(\operatorname{negative})
  \end{align*}
  Lowering this to MIR yields
  \begin{align*}
  &\deff \emptyf: (\{\}[] | .[]) \as \$x | .; \\
  &\deff \operatorname{select}(f): f \as \$x' | \ite{\$x'}{.}{\emptyf}; \\
  &\deff \operatorname{negative}: . \as \$x' | 0 \as \$y' | \$x' < \$y'; \\
  &.[] | \operatorname{select}(\operatorname{negative})
  \end{align*}
:::

@sec:semantics shows how to run the resulting MIR filter $f$.
For a given input value $v$, the output of $f$ will be given by $\eval\, \sem f\, v$.
