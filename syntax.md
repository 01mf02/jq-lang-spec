# Syntax {#sec:syntax}

We first describe the syntax for a large subset of the jq language in @sec:hir.
Next, we define a reduced subset of jq syntax called
intermediate representation (IR) in @sec:ir.
We provide a way to translate from jq syntax to IR.
We will use IR later to define the semantics in @sec:semantics.

## jq {#sec:hir}

We will now present a subset of jq syntax^[
  Actual jq syntax has a few more constructions to offer, including
  variable arguments, string interpolation, modules, etc.
  However, these constructions can be transformed into
  semantically equivalent syntax as treated in this text.
] of which we have already seen examples in @sec:tour.

A _filter_ $f$ is defined by the grammar
\begin{align*}
f &\coloneqq \quad n \gror s \gror . \gror .. \gror \$x \gror (f) \\
  &\gror [] \gror [f] \gror \{f: f, \dots, f: f\} \\
  &\gror f \star f \gror f \cartesian f \gror -f \gror f [p]^? \dots [p]^? \\
  &\gror f \jqas P | f \gror \jqfold{reduce}{f}{P}{(f; f)} \gror \jqfold{foreach}{f}{P}{(f; f; f)} \\
  &\gror {\jqlb{label}{x}} | f \gror {\jqlb{break}{x}} \\
  &\gror {\jqite{f}{f}{f}} \gror f? \gror \jqkw{try} f \gror \jqtc{f}{f} \\
  &\gror {\jqdef{x}{f} f} \gror \jqdef{x(x; \dots; x)}{f} f \\
  &\gror x \gror x(f; \dots; f)
\end{align*}
where:

- $p$ is a _position_ defined by the grammar $p \coloneqq \quad \emptyset \gror f \gror f: \gror :f \gror f:f$.
- $P$ is a _pattern_ defined by the grammar $P \coloneqq \quad \$x \gror [P, \dots, P] \gror \{f: P, \dots, f: P\}$.
- $x$ is an identifier (such as $\jqf{empty}$).
- $n$ is a number (such as $42$ or $3.14$).
- $s$ is a string (such as "Hello world!").

We use the superscript "$?$" to denote an optional presence of "?"; in particular,
$f [p]^? \dots [p]^?$ can be
$f [p]$, $f [p]?$,
$f [p] [p]$, $f [p]? [p]$, $f [p] [p]?$, $f [p]? [p]?$,
$f [p] [p] [p]$, and so on.
The potential instances of the operators $\star$ and $\cartesian$ are given in @tab:binops.
All operators $\star$ and $\cartesian$ are left-associative, except for
"`|`", "`=`", "`|=`", and "$\arith$`=`".

We will handle the operators `reduce` and `foreach` very similarly; therefore,
we introduce $\fold$ to stand for either `reduce` or `foreach`.
However, because `reduce` takes one argument less than `foreach`,
we simply ignore the superfluous argument when handling `reduce`.

| Name       | Symbol       | Operators                                                                      |
| ---------- | ------------ | ------------------------------------------------------------------------------ |
| Complex    | $\star$      | "`|`", "`,`", ("`=`", "`|=`", "$\arith$`=`", "`//=`"), "`//`", "`or`", "`and`" |
| Cartesian  | $\cartesian$ | (`==`, `!=`), (`<`, `<=`, `>`, `>=`), $\arith$                                 |
| Arithmetic | $\arith$     | (`+`, `-`), (`*`, `/`), `%`                                                    |

Table:
  Binary operators, given in order of increasing precedence.
  Operators surrounded by parentheses have equal precedence.
  {#tab:binops}

We consider equivalent the following notations^[
  Note that in jq, it is invalid syntax to
  call a nullary filter as `x()` instead of `x`, or to
  define a nullary filter as `def x(): f; g` instead of `def x: f; g`.
]:

- $f?$ and $\jqkw{try} f$
- $x$ and $x()$
- $\jqfold{foreach}{f_x}{P}{(f_y; f)}$ and
  $\jqfold{foreach}{f_x}{P}{(f_y; f; .)}$
- $\jqdef{x}{f} g$ and
  $\jqdef{x()}{f} g$
- $\jqkw{if} f_1 \jqkw{then} g_1 \jqkw{elif} f_2 \jqkw{then} g_2 \dots \jqkw{elif} f_n \jqkw{then} g_n \jqkw{else} h \jqkw{end}$ and \newline
  $\jqite{f_1}{g_1}{(\jqite{f_2}{g_2}{\dots (\jqite{f_n}{g_n}{h}) \dots})}$


## IR {#sec:ir}

We are now going to define IR filters and
show how to _lower_ a jq filter to an IR filter.
This allows us later to define semantics for IR
in a much less verbose way than for actual jq syntax.

An IR filter $f$ is defined by the grammar
\begin{align*}
f &\coloneqq \quad n \gror s \gror . \gror .. \gror \$x \\
  &\gror [] \gror [f] \gror \{\} \gror \{\$x: \$x\} \\
  &\gror f \star f \gror \$x \cartesian \$x \gror -\$x \gror .[p]^? \\
  &\gror f \jqas \$x | f \gror \jqfold{reduce}{f}{\$x}{(.; f)} \gror \jqfold{foreach}{f}{\$x}{(.; f; f)} \\
  &\gror {\jqite{\$x}{f}{f}} \gror \jqtc{f}{f} \\
  &\gror {\jqlb{label}{x}} | f \gror \jqlb{break}{x} \\
  &\gror {\jqdef{x(x; \dots; x)}{f} f} \\
  &\gror x(f; \dots; f)
\end{align*}
where $p$ is a position containing variables instead of filters as indices.

The set of complex operators $\star$ in IR is reduced compared to full jq syntax ---
for example, IR does not include "`=`" and "$\arith$`=`".
@tab:op-correspondence gives an exhaustive list of IR operators and
their corresponding operators in jq syntax.
In the remainder, we will use IR operators also in jq syntax.

-- --- --- --------- ------ ------- ------ --- ------ --- ------ --- --- -------- ------ ----
jq `|` `,` `|=`      `//`   `==`    `!=`   `<` `<=`   `>` `>=`   `+` `-` `*`      `/`    `%`
IR $|$ $,$ $\update$ $\alt$ $\iseq$ $\neq$ $<$ $\leq$ $>$ $\geq$ $+$ $-$ $\times$ $\div$ $\%$
-- --- --- --------- ------ ------- ------ --- ------ --- ------ --- --- -------- ------ ----

Table: Binary operators in concrete jq syntax and their corresponding IR operators. {#tab:op-correspondence}

Compared to actual jq syntax, IR filters
have simpler path operations
(such as $.[p]^?$ versus $f [p]^? \dots [p]^?$) and
replace certain occurrences of filters by variables
(e.g. $\$x \cartesian \$x$ versus $f \cartesian f$).

| $\varphi$ | $\floor \varphi$ |
| ----- | ------------ |
| $n$, $s$, $.$, $..$, $[]$, or $\{\}$ | $\varphi$ |
| $\$x$ or $\jqlb{break}{x}$ | $\varphi$ |
| $(f)$ | $\floor f$ |
| $[f]$ | $[\floor f]$ |
| $\{f: g\}$ | $\floor f \jqas \$x' | \floor g \jqas \$y' | \{\$x': \$y'\}$ |
| $\{f_1: g_1, \dots, f_n: g_n\}$ | $\floor{\{f_1: g_1\} + \dots + \{f_n: g_n\}}$ |
| $f$ `=` $g$ | $\floor g \jqas \$x' | \floor{f \update \$x'}$ |
| $f$ $\arith$`=` $g$ | $\floor g \jqas \$x' | \floor{f \update (. \arith \$x')}$ |
| $f$ `//=` $g$ | $\floor{f \update . \alt g}$ |
| $f \jqkw{and} g$ | $\floor{\jqite{f}{(g | \jqf{bool})}{\jqf{false}}}$ |
| $f \jqkw{or}  g$ | $\floor{\jqite{f}{\jqf{true}}{(g | \jqf{bool})}}$ |
| $f \star g$ | $\floor f \star \floor g$ |
| $f \cartesian g$ | $\floor f \jqas \$x' | \floor g \jqas \$y' | \$x' \cartesian \$y'$ |
| $-f$ | $\floor f \jqas \$x' | -\$x'$ |
| $f [p_1]^? \dots [p_n]^?$ | $. \jqas \$x' | \floor f | \floor{[p_1]^?}_{\$x'} | \dots | \floor{[p_n]^?}_{\$x'}$ |
| $f \jqas \$x | g$ | $\floor f \jqas \$x | \floor g$ |
| $f \jqas P | g$ | $\floor f \jqas \$x' | \floor{\$x' \jqas P | g}$,
| $\$x \jqas [P_1, \dots, P_n] | g$ | $\floor{\$x \jqas \obj{(0): P_1, \dots, (n-1): P_n} | g}$ |
| $\$x \jqas \obj{f_1: P_1, \dots} | g$ | $\floor{\$x[f_1] \jqas \$x' | \$x' \jqas P_1 | \$x \jqas \obj{f_2: P_2, \dots} | g}$ |
| $\$x \jqas \obj{} | g$ | $\floor g$ |
| $\jqfold{\fold}{f_x}{\$x}{(f_y; f; g)}$ | $. \jqas \$x' | \floor{f_y} | \jqfold{\fold}{(\floor{\$x'} | f_x)}{\$x}{(.; \floor f; \floor g)}$ |
| $\jqfold{\fold}{f_x}{P}{(f_y; f; g)}$ | $\floor{\jqfold{\fold}{(f_x \jqas P | \beta P)}{\$x'}{(f_y; \$x' \jqas \beta P | f; \$x' \jqas \beta P | g)}}$ |
| $\jqite{f_x}{f}{g}$ | $\floor{f_x} \jqas \$x' | \jqite{\$x'}{\floor f}{\floor g}$ |
| $f?$ | $\jqlb{label}{x'} | \jqtc{\floor f}{(\jqlb{break}{x'})}$ |
| $\jqtc{f}{g}$ | $\jqlb{label}{x'} | \jqtc{\floor f}{(\floor g, \jqlb{break}{x'})}$ |
| $\jqlb{label}{x} | f$ | $\jqlb{label}{x} | \floor f$ |
| $\jqdef{x}{f} g$ | $\jqdef{x}{\floor f} \floor g$ |
| $\jqdef{x(x_1; \dots; x_n)}{f} g$ | $\jqdef{x(x_1; \dots; x_n)}{\floor f} \floor g$ |
| $x(f_1; \dots; f_n)$ | $x(\floor{f_1}; \dots; \floor{f_n})$ |

Table: Lowering of a jq filter $\phi$ to an IR filter $\floor \phi$. {#tab:lowering}

@tab:lowering shows how to lower a jq filter $\varphi$ to
an equivalent IR filter $\floor \varphi$.
In particular, this desugars path operations and
makes it explicit which operations are Cartesian or complex.
By convention, we write $\$x'$ to denote a fresh variable.
Note that for some complex operators $\star$, namely
"`=`", "$\arith$`=`", "`//=`", "`and`", and "`or`",
@tab:lowering specifies individual lowerings, whereas
for the remaining complex operators $\star$, namely
"`|`", "`,`", "`|=`", and "`//`",
@tab:lowering specifies a uniform lowering
$\floor{f \star g} = \floor f \star \floor g$.

We define filters that yield the boolean values as
\begin{align*}
\jqf{true}  &\coloneqq (0 \iseq 0), \\
\jqf{false} &\coloneqq (0  \neq 0).
\end{align*}
The filter "$\jqf{bool} \coloneqq (\jqite{.}{\jqf{true}}{\jqf{false}})$"
maps its input to its boolean value.

In the lowering of the folding operators $\jqfold{\fold}{f_x}{P}{(f_y; f; g)}$
(where $\fold$ stands for either $\jqkw{reduce}$ or $\jqkw{foreach}$),
we replace the pattern $P$ by a variable by
"serialising" and "deserialising" the variables bound by $P$ with $\beta P$.
Here, $\beta P$ denotes the sequence of variables bound by $P$:
$$\beta P = \begin{cases}
  \sum_i \beta P_i & \text{if $P = [P_1, \dots, P_n]$ or $P = \{f_1: P_1, \dots, f_n: P_n\}$} \\
  [\$x] & \text{if $P = \$x$}
\end{cases}$$
(We used $\sum_i x_i = x_1 + \dots + x_n$ and $[x_1, \dots, x_n] + [y_1, \dots, y_m] = [x_1, \dots, x_n, y_1, \dots, y_m]$.)
In particular, we exploit the property that
$f \jqas P | g$ can be rewritten to
$$ f \jqas P | \beta P \jqas \$x' | \$x' \jqas \beta P | g, $$
because $\beta P$ can be interpreted both as pattern and as filter.

::: {.example}
Consider the filter $\varphi \equiv f \jqas [\$x, [\$y], \$z] | g$.
This filter destructures all outputs of $f$ that are of the shape
$[x, [y, \dots], z, \dots]$ and binds the values
$x$, $y$, and $z$ to the respective variables.
Here, $\varphi$ uses the pattern
$P = [\$x, [\$y], \$z]$ for which
$\beta P = [\$x, \$y, \$z]$.
It holds that $\varphi$ is equivalent to
$$ f \jqas [\$x, [\$y], \$z] | [\$x, \$y, \$z] \jqas \$x' | \$x' \jqas [\$x, \$y, \$z] | g. $$
Here, we first used $\beta P$ as filter
($[\$x, \$y, \$z] \jqas \$x' | \dots$) to "serialise" the pattern variables to an array, then as pattern
($\$x' \jqas [\$x, \$y, \$z] | \dots$) to "deserialise" the array to retrieve the pattern variables.
:::

| $[p]  ^?$ | $\floor{[p]^?}_{\$x}$ |
| --------- | ---------------------- |
| $[   ]^?$ | $.[]^?$
| $[f  ]^?$ | $(\$x | \floor f) \jqas \$y' | .[\$y']^?$ |
| $[f: ]^?$ | $(\$x | \floor f) \jqas \$y' | .[\$y':]^?$ |
| $[ :f]^?$ | $(\$x | \floor f) \jqas \$y' | .[:\$y']^?$ |
| $[f:g]^?$ | $(\$x | \floor f) \jqas \$y' | (\$x | \floor g) \jqas \$z' | .[\$y':\$z']^?$ |

Table: Lowering of a position $[p]^?$ with input $\$x$ to an IR filter. {#tab:lower-path}

@tab:lower-path shows how to lower a position $[p]^?$ to IR filters.
Like in @sec:hir, the meaning of superscript "$?$" is an optional presence of "$?$".
In the lowering of $f [p_1]^? \dots [p_n]^?$ in @tab:lowering,
if $[p_i]$ in the first column is directly followed by "?", then
$\floor{[p_i]^?}_{\$x}$ in the second column stands for
$\floor{[p_i] ?}_{\$x}$, otherwise for
$\floor{[p_i]  }_{\$x}$.
Similarly, in @tab:lower-path, if $[p]$ in the first column is followed by "$?$", then
all occurrences of superscript "?" in the second column stand for "?", otherwise for nothing.

::: {.example}
The jq filter $(.[]?[])$ is lowered to
$(. \jqas \$x' | . | .[]? | .[])$.
Semantically, we will see that this is equivalent to $(.[]? | .[])$.
:::

::: {.example}
The jq filter $\mu \equiv .[0]$ is lowered to
$\floor \mu \equiv (. \jqas \$x | . | (\$x | 0) \jqas \$y | .[\$y])$.
Semantically, we will see that $\floor \mu$ is equivalent to $(0 \jqas \$y | .[\$y])$.
The jq filter $\varphi \equiv ([3] | .[0] = (\jqf{length}, 2))$
is lowered to the IR filter
$\floor \varphi \equiv ([3] | (\jqf{length}, 2) \jqas \$z | \floor \mu \update \$z)$.
In @sec:semantics, we will see that its output is $\stream{[1], [2]}$.
:::

The lowering in @tab:lowering is compatible with the semantics of `jq`,
with one notable exception:
In `jq`, Cartesian operations $f \cartesian g$ would be lowered to
$\floor g \jqas \$y' | \floor f \jqas \$x' | \$x \cartesian \$y$, whereas we lower it to
$\floor f \jqas \$x' | \floor g \jqas \$y' | \$x \cartesian \$y$,
thus inverting the binding order.
Note that the difference only shows when both $f$ and $g$ return multiple values.
We diverge here from `jq` to make the lowering of Cartesian operations
consistent with that of other operators, such as $\{f: g\}$, where
the leftmost filter ($f$) is bound first and the rightmost filter ($g$) is bound last.
That also makes it easier to describe other filters, such as
$\{f_1: g_1, \dots, f_n: g_n\}$, which we can lower to
$\floor{\{f_1: g_1\} + \dots + \{f_n: g_n\}}$, whereas its lowering assuming the jq lowering of Cartesian operations would be
$$\floor{\{f_1: g_1\}} \jqas \$x'_1 | \dots | \floor{\{f_n: g_n\}} \jqas \$x'_n | \$x'_1 + \dots + \$x'_n.$$

::: {.example}
The filter $(0, 2) + (0, 1)$ yields
$\stream{0, 1, 2, 3}$ using our lowering, and
$\stream{0, 2, 1, 3}$ in `jq`.
:::

\newcommand{\wf}{\operatorname{wf}}
Informally, we say that a filter is _wellformed_ if all references to
named filters, variables, and labels were previously bound.
For example, the filter "$a, \$x$" is not wellformed because
neither $a$ nor $\$x$ was previously bound, but the filter
"$\jqdef{a}{1} 2 \jqas \$x | a, \$x$" is wellformed.
@tab:wf specifies in detail if a filter is wellformed.
For this, it uses a context $c = (d, v, l)$, consisting of
a set $d$ of pairs $(x, n)$ storing the name $x$ and the arity $n$ of a filter,
a set $v$ of variables, and
a set $l$ of labels.
We say that a filter $\varphi$ is wellformed with respect to a context $c$ if
$\wf(\varphi, c)$ is true.

| $\varphi$ | $\wf(\varphi, c)$ |
| --------- | ----------------- |
| $n$, $s$, $.$, $..$, $[]$, or $\{\}$ | $\top$ |
| $\$x$ or $-\$x$   | $\$x \in v$ |
| $\jqlb{break}{x}$ | $\$x \in l$ |
| $[f]$ | $\wf(f, c)$ |
| $\{\$x: \$y\}$ or $\$x \cartesian \$y$ | $\$x \in v$ and $\$y \in v$ |
| $f \star g$ or $\jqtc{f}{g}$ | $\wf(f, c)$ and $\wf(g, c)$ |
| $.[p]^?$ | $\forall \$x \in p.\ \$x \in v$ |
| $f \jqas \$x | g$ | $\wf(f, c)$ and $\wf(g, (d, v \cup \{\$x\}, l))$ |
| $\jqlb{label}{x} | f$ | $\wf(f, (d, v, l \cup \{\$x\}))$ |
| $\jqite{\$x}{f}{g}$ | $\$x \in v$ and $\wf(f, c)$ and $\wf(g, c)$ |
| $\jqfold{\fold}{f_x}{\$x}{(.; f; g)}$ | $\wf(f_x, c)$ and $\wf((f | g), (d, v \cup \{\$x\}, l))$ |
| $\jqdef{x(x_1; \dots; x_n)}{f} g$ | $\wf(f, (d \cup \{(x, n)\} \cup \bigcup_i \{(x_i, 0)\}, v, l))$ and $\wf(g, (d \cup \{(x, n)\}, v, l))$ |
| $x(f_1; \dots; f_n)$ | $(x, n) \in d$ and $\forall i. \wf(f_i, c)$ |

Table: Wellformedness of an IR filter $\varphi$ with respect to a context $c = (d, v, l)$. {#tab:wf}

For hygienic reasons, we require that labels are disjoint from variables.
This can be easily ensured by prefixing labels and variables differently.

::: {.example}
Consider the filter $\jqlb{label}{x} | . \jqas \$x | \$x + \$x, \jqlb{break}{x}$.
Here, we have to rename to ensure that labels and variables are disjoint, yielding e.g.
$\jqlb{label}{l_x} | . \jqas \$v_x | \$v_x + \$v_x, \jqlb{break}{l_x}$.
:::

Furthermore, we require that identifiers with the same name represent filters with equal arity.
This can be ensured by postfixing all identifiers with their arity.

::: {.example}
Consider the filter $\jqdef{f(g)}{g} \jqdef{f}{.} f(f)$.
Here, we have to rename identifiers to prevent shadowing issues in the semantics, yielding e.g.
$\jqdef{f^1(g^0)}{g^0} \jqdef{f^0}{.} f^1(f^0)$.
:::

::: {.example}
Consider the jq filter $\jqdef{\jqf{recurse}(f)}{., (f | \jqf{recurse}(f))} \jqf{recurse}(. + 1)$,
which returns the infinite stream of output values $n, n+1, \dots$
when provided with an input number $n$.
Lowering this to IR yields
$\jqdef{\jqf{recurse}(f)}{., (f | \jqf{recurse}(f))} \jqf{recurse}(. \jqas \$x' | 1 \jqas \$y' | \$x' + \$y')$.
:::

::: {.example}
Consider the following jq program:
\begin{align*}
&\jqdef{\jqf{empty}}{(\{\}[]) \jqas \$x | .} \\
&\jqdef{\jqf{select}(f)}{\jqite{f}{.}{\jqf{empty}}} \\
&\jqdef{\jqf{negative}}{. < 0} \\
&.[] | \jqf{select}(\jqf{negative})
\end{align*}
When given an array as an input, it yields
those elements of the array that are smaller than $0$.^[
  The filter `empty` returns an empty stream.
  We might be tempted to define it as `{}[]`,
  which constructs an empty object, then returns its contained values,
  which corresponds to an empty stream as well.
  However, such a definition relies on the temporary construction of new values
  (such as the empty object here),
  which is not admissible on the left-hand side of updates (see @sec:updates).
  To ensure that `empty` can be employed also as a path expression,
  we define it in this complicated manner.
]
Lowering this to IR yields
\begin{align*}
&\jqdef{\jqf{empty}}{(. \jqas \$x' | \{\} | .[]) \jqas \$x | .} \\
&\jqdef{\jqf{select}(f)}{f \jqas \$x' | \jqite{\$x'}{.}{\jqf{empty}}} \\
&\jqdef{\jqf{negative}}{. \jqas \$x' | 0 \jqas \$y' | \$x' < \$y'} \\
&. \jqas \$x' | . | .[] | \jqf{select}(\jqf{negative})
\end{align*}
:::

@sec:semantics shows how to run an IR filter $f$.
For a given input value $v$, the output of $f$ will be given by $\eval\, \sem f\, v$.
