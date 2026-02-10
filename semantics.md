# Evaluation Semantics {#sec:semantics}

In this section, we will show how to transform --- or compile ---
an IR filter $\varphi$ to a lambda term $\sem \varphi$ of type $\filtert$.
We will then define a function "$\eval\, \varphi\, v$" that
returns the list of value-path results that
the filter $\varphi: \filtert$ outputs when given
the value-path $v: \valpatht$ as input.
The evaluation strategy is call-by-name.

## Compilation

A compiled filter $\filtert$ is
a pair of a _run_ and an _update_ function.
We can obtain the run and update functions from a compiled filter as follows:
\begin{alignat*}{3}
\run&{}: \filtert \to (\valpatht \to \stream{\resultt\, \valpatht}) &&\coloneqq \fst \\
\upd&{}: \filtert \to (\valt \to \stream{\resultt\, \valt}) \to \valt \to \stream {\resultt\, \valt} &&\coloneqq \snd
\end{alignat*}
The lambda term $\sem \varphi : \filtert$ corresponding to an IR filter $\varphi$ has the shape
$$\sem \varphi = \pair\, (\lambda v. t_r)\, (\lambda \sigma\, v. t_u)$$
for some terms $t_r$ (run function) and $t_u$ (update function).
For a given $\varphi$, we can obtain
$t_r$ by "$\run\, \sem \varphi\, v$" and
$t_u$ by "$\upd\, \sem \varphi\, \sigma\, v$".
For conciseness, we write
"$\run\, \sem \varphi\, v$" to define $t_r$ and
"$\upd\, \sem \varphi\, \sigma\, v$" to define $t_u$.

::: {.example name="Identity filter compilation"}
For the identity filter "$.$", we have $$ \sem{.} = \pair\,
(\lambda v. \stream{\ok v})\,
(\lambda \sigma\, v. \sigma\, v), $$ where
$t_r = \stream{\ok v}$ was obtained from @tab:eval-semantics and
$t_u = \sigma\, v$ was obtained from @tab:update-semantics.
:::

\newcommand{\fresh}{\kappa}

The lambda term $\sem \varphi$ obtained from a well-formed filter $\varphi$
may contain at most one free variable, namely $\fresh$.
This variable is used to generate fresh labels for the execution of
$\jqlb{label}{x} | f$, see @ex:labels.
In order to create a closed term, we initially bind $\fresh$ to zero.
We can then run a filter using the following function:
$$\eval: \filtert \to \valt \to \stream{\resultt\, \valt} \coloneqq \lambda \varphi. (\lambda \fresh. \run\, \varphi)\, \zero$$

\newcommand{\reducef }{\operatorname{reduce }}
\newcommand{\foreachf}{\operatorname{foreach}}
\newcommand{\untilf}{\operatorname{until}}
\newcommand{\labelf}{\operatorname{label}}

Table: Evaluation semantics. {#tab:eval-semantics}

| $\varphi$ | $\run\, \sem \varphi\, v$ |
| --------- | ------------------------- |
| $n$ or $s$ | $\stream{\ok \varphi}$ |
| $.$ | $\stream{\ok v}$ |
| $..$ | $\run\, \sem{\jqdef{r}{., (.[]? | r)} r}\, v$ |
| $\$x$ | $\stream{\ok \$x}$ |
| $[  ]$ | $\stream{\arr\, \stream{}}$ |
| $\{\}$ | $\stream{\ok \objf_0}$ |
| $[f ]$ | $\stream{\arr\, (\run\, \sem f\, v)}$ |
| $\{\$x: \$y\}$ | $\stream{\objf_1\, \$x\, \$y}$ |
| $\$x \arith \$y$ | $\stream{\$x \arith \$y}$ |
| $\$x \cartesian \$y$ | $\stream{\ok{(\$x \cartesian \$y)}}$ |
| $-\$x$ | $\stream{- \$x}$ |
| $f, g$ | $\run\, \sem f\, v + \run\, \sem g\, v$ |
| $f | g$ | $\run\, \sem f\, v \bind \run\, \sem g$ |
| $f \alt g$ | $(\run\, \sem f\, v \bind \trues)\, (\lambda h\, t. \stream h + t)\, (\run\, \sem g\, v)$ |
| $f \jqas \$x | g$ | $\run\, \sem f\, v \bind (\lambda \$x. \run\, \sem g\, v)$ |
| $\jqtc{f}{g}$ | $\run\, \sem f\, v \bind_L \lambda r. r\, (\lambda o. \stream r)\, (\run\, \sem g)\, (\lambda b. \stream r)$ |
| $\jqlb{label}{x} | f$ | $\labelf \fresh\, ((\lambda \$x\, \fresh. \run\, \sem f\, v)\, \fresh\, (\operatorname{succ}\, \fresh))$ |
| $\jqlb{break}{x}$ | $\stream{\breakf\, \$x}$ |
| $\jqite{\$x}{f}{g}$ | $\run\, ((\bool\, \$x)\, \sem f\, \sem g)\, v$ |
| $.[p]^?$ | $v[p]^?$ |
| $\jqfold{reduce }{f_x}{\$x}{(.; f   )}$ | $\reducef \, (\lambda \$x. \run\, \sem f)\, (\run\, \sem{f_x}\, v)\, v$ |
| $\jqfold{foreach}{f_x}{\$x}{(.; f; g)}$ | $\foreachf\, (\lambda \$x. \run\, \sem f)\, (\lambda \$x. \run\, \sem g)\, (\run\, \sem{f_x}\, v)\, v$ |
| $\jqdef{x(x_1; ...; x_n)}{f} g$ | $(\lambda x. \run\, \sem g\, v) (Y\, (\lambda x\, x_1\, ...\, x_n. \sem f))$ |
| $x(f_1; ...; f_n)$ | $\run\, (x\, \sem{f_1}\, ...\, \sem{f_n})\, v$ |
| $f \update g$ | $\upd\, \sem f\, (\run\, \sem g)\, v$ |

The evaluation semantics are given in @tab:eval-semantics.
Let us discuss its different cases:

- $n$ or $s$: Returns the value corresponding to the number $n$ or string $s$.
- "$.$": Returns the input value. This is the identity filter.
- "$..$": Returns the input value and all values recursively contained within it.
- $\$x$: Returns the value currently bound to the variable $\$x$.
  Wellformedness of the filter (as defined in @sec:ir) ensures that
  whenever we evaluate a variable, it must have been substituted by a concrete value,
  for example by a surrounding call to $f \jqas \$x | g$.
- $[]$ or $\{\}$: Creates an empty array or object.
- $[f]$: Creates an array from the output of $f$, using the function $\arr$ defined in @sec:values.
- $\{\$x: \$y\}$: Creates an object from the values bound to $\$x$ and $\$y$,
  using the function $\objf_1$ defined in @sec:values.
- $\$x \arith \$y$: Returns the output of an arithmetic operation "$\arith$"
  (any of $+$, $-$, $\times$, $\div$, and $\%$, as given in @tab:op-correspondence)
  on the values bound to $\$x$ and $\$y$.
- $\$x \cartesian \$y$: Returns the output of a Boolean operation "$\cartesian$"
  (any of $\stackrel{?}{=}$, $\neq$, $<$, $\leq$, $>$, $\geq$, as given in @tab:op-correspondence)
  on the values bound to $\$x$ and $\$y$.
  Because we assumed that Boolean operations return $\valt$ and are thus infallible
  (unlike the arithmetic operations $\arith$, which return $\resultt\, \valt$),
  we have to wrap their outputs with an $\ok$.
- $f, g$: Concatenates the outputs of $f$ and $g$, both applied to the same input.
- $f | g$: Composes $f$ and $g$, returning the outputs of $g$ applied to all outputs of $f$.
- $f \alt g$: Let $l$ be the outputs of $f$ whose boolean values are not false.
  This filter returns $l$ if $l$ is not empty, else the outputs of $g$.
  Here, we use a function "$\trues$" that
  returns its input if its boolean value is true.
  $$\trues: \valpatht \to \stream{\resultt\, \valpatht} \coloneqq \lambda x. (\bool\, x)\, \stream{\ok\, x}\, \stream{}$$
- $f \jqas \$x | g$: For every output of $f$, binds it to the variable $\$x$ and
  returns the output of $g$, where $g$ may reference $\$x$.
  Unlike $f | g$, this runs $g$ with the original input value instead of an output of $f$.
  We can show that the evaluation of $f | g$ is equivalent to that of
  $f \jqas \$x' | \$x' | g$, where $\$x'$ is a fresh variable.
  Therefore, we could be tempted to lower $f | g$ to
  $\floor f \jqas \$x' | \$x' | \floor g$ in @tab:lowering,
  in order to further simplify IR and thus the semantics.
  However, we cannot do this because we will see in @sec:updates that
  this equivalence does _not_ hold for updates; that is,
  $(f | g) \update \sigma$ is _not_ equal to
  $(f \jqas \$x' | \$x' | g) \update \sigma$.
- $\jqtc{f}{g}$: Replaces all outputs of $f$ that equal "$\err\, e$" for some $e$
  by the output of $g$ on the input $e$.
  At first sight, this seems to diverge from jq, which
  aborts the evaluation of $f$ after the first error.
  However, because lowering to IR replaces
  $\jqkw{try} f \jqkw{catch} g$ with
  $\jqlb{label}{x'} | \jqtc{f}{(g, \jqlb{break}{x'})}$ (see @tab:lowering),
  the overall behaviour described here corresponds to jq after all.
- $\jqlb{label}{x} | f$: Returns all values yielded by $f$ until $f$ yields
  an exception "$\breakf\, \$x$".
  This uses a function "$\labelf$" that
  takes a label $\fresh$ and a list $l$ of value results,
  returning the longest prefix of $l$ that does not contain $\breakf\, \fresh$:
  \begin{alignat*}{3}
  \untilf&{}: (\resultt \to \mathbb B) &{}\to{}& \listt \to \listt \coloneqq
  \lambda p\, l. l\, (\lambda h\, t. p\, h\, \stream{}\, (\stream h + \untilf\, p\, t)) \\
  \labelf&{}: \mathbb N &\to{}& \listt \to \listt \coloneqq
  \lambda \fresh. \untilf\, (\lambda r. r\, (\lambda o. \false)\, (\lambda e. \false)\, (\lambda b. \operatorname{nat\_eq}\, \fresh\, b))
  \end{alignat*}
  Here,
  $\nateq: \mathbb N \to \mathbb N \to \boolt$ returns
  $\true$ if two natural numbers are equal, else $\false$.
- $\jqlb{break}{x}$: Returns a value result "$\breakf\, \$x$".
  Similarly to the evaluation of variables $\$x$ described above,
  wellformedness of the filter (as defined in @sec:hir) ensures that
  the returned value $\breakf\, \$x$ will be
  eventually handled by a corresponding filter
  $\jqlb{label}{x} | f$.
  That means that $\eval \sem \varphi$ for a wellformed filter $\varphi$ can only yield
  values and errors, but never a break result.
- $\jqite{\$x}{f}{g}$: Returns the output of $f$ if $\$x$ is bound to
  a "true" value (neither null nor false for JSON, see @sec:json), else returns the output of $g$.
- $.[p]^?$: Accesses parts of the input value;
  see @sec:value-ops for the definitions of the operators.
  When evaluating this, the indices contained in $p$ have been substituted by values.
- $\jqfold{\fold}{f_x}{\$x}{(.; f; g)}$: Folds $f$ over the values returned by $f_x$,
  starting with the current input as accumulator.
  The current accumulator value is provided to $f$ as input value and
  $f$ can access the current value of $f_x$ by $\$x$.
  If $\fold =  \jqf{reduce}$, this returns only the final        values of the accumulator, whereas
  if $\fold = \jqf{foreach}$, this returns also the intermediate values of the accumulator.
  We will further explain this and define the functions
  "$\reducef  f\,     l\, v$" and
  "$\foreachf f\, g\, l\, v$" in @sec:folding.
- $\jqdef{x(x_1; ...; x_n)}{f} g$: Binds the $n$-ary filter $x$ in $g$.
  The definition of $x$, namely $f$, may refer to
  any of the arguments $x_i$ as well as to $x$ itself.
  In other words, filters can be defined recursively,
  which is why we use the $Y$ combinator here.
  @ex:recursion shows how a recursive call is evaluated.
- $x(f_1; ...; f_n)$: Calls an $n$-ary filter $x$.
  This also handles the case of calling nullary filters such as $\jqf{empty}$.
- $f \update g$: Updates the input at positions returned by $f$ by $g$.
  We will discuss this in @sec:updates.

<!-- TODO: explain how to handle builtin filters implemented by definition and as native function -->
An implementation may also define semantics for builtin named filters, for example:
\begin{align*}
\run\, \sem{\jqf{error}}\, v &\coloneqq \stream{\err\, v} \\
\run\, \sem{\jqf{path}(f)}\, v &\coloneqq \run\, \sem{f}\, v \bind \lambda v. \stream{\snd\, v\, (\lambda p. \arr\, (\mapl\, \ok\, p))\, (\err\, \dots)}
\end{align*}
In particular, $\jqf{path}(f)$ is an important filter that
runs $f$ and returns the path of each output ($\snd\, v$) as array,
yielding an error if an output does not have an associated path.
<!-- and
$\run\, \sem{\jqf{keys }}\, v \coloneqq \stream{\arr\, (\keys\, v)}$, see @sec:simple-fns.
In the case of $\jqf{keys}$, for example, there is no obvious way to implement it by definition,
in particular because there is no simple way to obtain the domain of an object $\{...\}$
using only the filters for which we gave semantics in @tab:eval-semantics-->

::: {.example #ex:recursion name="Recursion"}
  Consider the following IR filter $\varphi$: $$\jqdef{\jqf{repeat}}{., \jqf{repeat}} \jqf{repeat}$$
  This filter repeatedly outputs its input;
  for example, given the input $v = 1$, it returns $\stream{\ok 1, \ok 1, \ok 1, ...}$.
  First, let us compile a part of our filter, namely
  $$\rho = \sem{., \jqf{repeat}} =^{\sem \cdot} \pair\, (\lambda v. \stream{\ok v} + \run\, \jqf{repeat}\, v)\, (...).$$
  Here, the second part of the pair $(...)$ does not matter, because
  it is never evaluated due to our not performing any updates in this example.

  Now, we can evaluate the filter $\varphi$ by
  $\eval\, \sem \varphi\, v = (\lambda \fresh. \run\, \sem \varphi)\, \zero\, v$.
  Because $\varphi$ does not contain any labels,
  $\sem \varphi$ does not make any reference to $\fresh$, therefore
  $\eval\, \sem \varphi\, v$ is equivalent to:
  \allowdisplaybreaks
  \begin{align*}
  \run\, \sem \varphi\, v
  &= (\lambda \jqf{repeat}. \run\, \sem{\jqf{repeat}}\, v)\, (Y\, (\lambda \jqf{repeat}. \rho)) \\
  &=^{\sem \cdot} (\lambda \jqf{repeat}. \run\, \jqf{repeat}\, v)\, (Y\, (\lambda \jqf{repeat}. \rho)) \\
  &=^\beta \run\, (Y\, (\lambda \jqf{repeat}. \rho))\, v \\
  &=^Y \run\, ((\lambda \jqf{repeat}. \rho)\, (Y\, (\lambda \jqf{repeat}. \rho)))\, v \\
  &=^\rho \run\, ((\lambda \jqf{repeat}. \pair\, (\lambda v. \stream{\ok v} + \run\, \jqf{repeat}\, v)\, (...))\, (Y\, (\lambda \jqf{repeat}. \rho)))\, v \\
  &=^\beta \run\, (\pair\, (\lambda v. \stream{\ok v} + \run\, (Y\, (\lambda \jqf{repeat}. \rho))\, v)\, (...))\, v \\
  &=^\beta \stream{\ok v} + \run\, (Y\, (\lambda \jqf{repeat}. \rho))\, v \\
  &= \stream{\ok v} + \run\, \sem \varphi\, v.
  \end{align*}
  This shows that the evaluation of $\varphi$ on any input $v$ yields
  an infinite stream of $\ok v$ results.
:::

::: {.example #ex:labels name="Labels"}
  Let us consider the filter $\varphi \equiv \jqlb{label}{x} | \jqlb{break}{x}$.
  We have:
  \begin{align*}
  \eval\, \sem \varphi\, v
  &= (\lambda \fresh. \run \sem{\jqlb{label}{x} | \jqlb{break}{x}})\, \zero\, v \\
  &= (\lambda \fresh\, v. \labelf\, \fresh\, ((\lambda \$x\, \fresh. \run\, \sem{\jqlb{break}{x}}\, v)\, \fresh\, (\succf\, \fresh)))\, \zero\, v \\
  &= \labelf\, \zero\, ((\lambda \$x\, \fresh. \stream{\jqlb{break}{x}})\, \zero\, (\succf\, \zero)) \\
  &= \labelf\, \zero\, \stream{\breakf\, \zero} \\
  &= \stream{}
  \end{align*}
  It is interesting to note that if instead of $\jqlb{break}{x}$,
  we would have used a more complex filter, e.g. $\jqlb{label}{y} | ...$,
  then $\$y$ would have been substituted by $\succf\, \zero$
  (which we can already see in our large equation above).
  This mechanism reliably allows us to generate fresh labels and to
  differentiate for each $\breakf$ the corresponding $\labelf$ that handles it.
:::

## Folding {#sec:folding}

In this subsection, we will define the functions
$\reducef$ and $\foreachf$ which underlie the semantics for the folding operators
$\jqfold{reduce }{f_x}{\$x}{(.; f)}$ and
$\jqfold{foreach}{f_x}{\$x}{(.; f; g)}$.

\newcommand{\foldf}{\operatorname{fold}}
Let us start by defining a general folding function "$\foldf$":
\begin{align*}
\foldf&{}: (T \to U \to \stream{\resultt\, U}) \to (T \to U \to \stream{\resultt\, U}) \to (U \to \stream{\resultt\, U}) \to \stream{\resultt\, T} \to U \to \stream{\resultt\, U} \\
&\coloneqq \lambda f\, g\, n. Y_2\, (\lambda F\, l\, v. l\, (\lambda h\, t. f\, h\, v \bind (\lambda y. g\, h\, y + F\, t\, y))\, (n\, v))
\end{align*}
Here,
$T$ is the type of list elements that the fold iterates over, and
$U$ is the type of the accumulator.
When we use this function later,
both $T$ and $U$ will be instantiated with $\valpatht$ ---
we distinguish between $T$ and $U$ here to clarify
the difference between list elements and the accumulator.

This function takes
two functions $f$ and $g$ that both
take a list element and an accumulator and return a list of accumulator results, and
a function $n$ (for the nil case) from a final accumulator $x$ to a list of accumulator results.
From that, it creates a recursive function that
takes a list of results $l$ and an initial accumulator $v$ and
returns a list of accumulator results.
This function folds over the elements in $l$, starting from the accumulator value $v$.
For every element $h$ in $l$,
$f$ is evaluated with $h$ and the current accumulator value $v$ as input.
Every output $y$ of $f$ is output after passing through $g$, then
used as new accumulator value with the remaining list $t$.
If $l$ is empty, then $v$ is called a _final_ accumulator value and $n\, v$ is returned.

We use two different functions for $n$;
the first returns just its input, corresponding to $\jqf{reduce}$ which returns a final value, and
the second returns nothing,  corresponding to $\jqf{foreach}$.
Instantiating "$\foldf$" with these two functions, we obtain the following:
\begin{alignat*}{4}
\reducef &\coloneqq \lambda f.     && \foldf\, f\, (\lambda h\, v. \stream{})\, && (\lambda v. \stream{\ok v &&}) \\
\foreachf &\coloneqq \lambda f\, g. && \foldf\, f\, g\, && (\lambda v. \stream{&&})
\end{alignat*}
Here, "$\reducef$" and "$\foreachf$" are the functions used in @tab:eval-semantics.
Their types are:
\begin{alignat*}{2}
\reducef &{}: (T \to U \to \stream{\resultt\, U}) &&\to \stream{\resultt\, T} \to U \to \stream{\resultt\, U} \\
\foreachf&{}: (T \to U \to \stream{\resultt\, U}) \to (T \to U \to \stream{\resultt\, U}) &&\to \stream{\resultt\, T} \to U \to \stream{\resultt\, U}
\end{alignat*}
We will now look at what the evaluation of the various folding filters expands to.
Assuming that the filter $f_x$ evaluates to $\stream{x_0, ..., x_n}$,
then $\jqf{reduce}$ and $\jqf{foreach}$ expand to
\begin{alignat*}{2}
\jqfold{reduce }{f_x}{\$x}{(.; f   )} ={}& x_0 \jqas \$x | f & \quad
\jqfold{foreach}{f_x}{\$x}{(.; f; g)} ={}& x_0 \jqas \$x | f | g, ( \\
|\; & ... &
    & ... \\
|\; & x_n \jqas \$x | f &
    & x_n \jqas \$x | f | g, ( \\
    &     &
    & \jqf{empty})...)
\end{alignat*}
Note that jq implements only restricted versions of these folding operators
that consider only the last output of $f$ for the next iteration.
That means that in jq,
$\jqfold{reduce}{f_x}{\$x}{(.;            f )}$ is equivalent to
$\jqfold{reduce}{f_x}{\$x}{(.; \jqf{last}(f))}$.
Here, we assume that the filter $\jqf{last}(f)$
returns the last output of $f$ if $f$ yields any output, else nothing.
<!-- TODO: write about jq limitation of recording paths with folding operators -->


# Update Semantics {#sec:updates}

In this section, we will discuss how to evaluate updates $f \update g$.
First, we show the path-based update semantics used in most jq implementations,
and show which problems this approach entails.
Then, we introduce our alternative, path-less update semantics, which
avoid many problems of path-based updates, while
enabling higher performance by forgoing the construction of temporary path data.

## Path-based updates {#sec:jq-updates}

jq's update mechanism works with _paths_.
A path is a sequence of indices $i_j$ that can be written as $.[i_1]...[i_n]$.
It refers to a value that can be retrieved by the filter "$.[i_1] | ... | .[i_n]$".
Note that "$.$" is a valid path, referring to the input value.

The update operation "$f \update g$" attempts to
first obtain the paths of all values returned by $f$,
then for each path, it replaces the value at the path by $g$ applied to it.
Note that $f$ is not allowed to produce new values; it may only return paths.

::: {.example #ex:arr-update}
  Consider the input value $[[1, 2], [3, 4]]$.
  We can retrieve the arrays $[1, 2]$ and $[3, 4]$ from the input with the filter "$.[]$", and
  we can retrieve the numbers 1, 2, 3, 4 from the input with the filter "$.[] | .[]$".
  To replace each number with its successor, we run "$(.[] | .[]) \update .+1$",
  obtaining $[[2, 3], [4, 5]]$.
  Internally, in jq, this first builds the paths
  $.[0][0]$, $.[0][1]$, $.[1][0]$, $.[1][1]$,
  then updates the value at each of these paths with $g$.
:::

This approach can yield surprising results when the execution of the filter $g$
changes the input value in a way that the set of paths changes midway.
In such cases, only the paths constructed from the initial input are considered.
This can lead to
paths pointing to the wrong data,
paths pointing to non-existent data, and
missing paths.

::: {.example #ex:obj-update-arr}
  Consider the input value $\obj{\jqstr{a} \mapsto \obj{\jqstr{b} \mapsto 1}}$ and the filter
  $(.[], .[][]) \update g$, where $g$ is $[]$.
  Executing this filter in jq first builds the path
  $.[\jqstr{a}]$ stemming from "$.[]$", then
  $.[\jqstr{a}][\jqstr{b}]$ stemming from "$.[][]$".
  Next, jq folds over the paths,
  using the input value as initial accumulator and
  updating the accumulator at each path with $g$.
  The final output is thus the output of
  $(.[\jqstr{a}] \update g) | (.[\jqstr{a}][\jqstr{b}] \update g)$.
  The output of the first step $.[\jqstr{a}] \update g$ is $\obj{\jqstr{a} \mapsto []}$.
  This value is the input to the second step $.[\jqstr{a}][\jqstr{b}] \update g$,
  which yields an error because
  we cannot index the array $[]$ at the path $.[\jqstr{a}]$ by $.[\jqstr{b}]$.
:::

We can also have surprising behaviour that does not manifest any error.

::: {.example #ex:obj-update-obj}
  Consider the same input value and filter as in @ex:obj-update-arr,
  but now with $g$ set to $\obj{\jqstr{c}: 2}$.
  The output of the first step $.[\jqstr{a}] \update g$ is $\obj{\jqstr{a} \mapsto \obj{\jqstr{c} \mapsto 2}}$.
  This value is the input to the second step $.[\jqstr{a}][\jqstr{b}] \update g$, which yields
  $\obj{\jqstr{a} \mapsto \obj{\jqstr{c} \mapsto 2, \jqstr{b} \mapsto \obj{\jqstr{c} \mapsto 2}}}$.
  Here, the remaining path ($.[\jqstr{a}][\jqstr{b}]$) pointed to
  data that was removed by the update on the first path,
  so this data gets reintroduced by the update.
  On the other hand, the data introduced by the first update step
  (at the path $.[\jqstr{a}][\jqstr{c}]$) is not part of the original path,
  so it is _not_ updated.
:::

We found that we can interpret many update filters by simpler filters,
yielding the same output as jq in most common cases, but avoiding the problems shown above.
To see this, let us see what would happen if we would interpret
$(f_1, f_2) \update g$ as $(f_1 \update g) | (f_2 \update g)$.
That way, the paths of $f_2$ would point precisely to the data returned by
$f_1 \update g$, thus avoiding the problems depicted by the examples above.
In particular, with such an approach,
@ex:obj-update-arr would yield $\obj{\jqstr{a} \mapsto []}$ instead of an error, and
@ex:obj-update-obj would yield $\obj{\jqstr{a} \mapsto \obj{\jqstr{c} \mapsto \obj{\jqstr{c} \mapsto 2}}}$.

In the remainder of this section, we will show
semantics that extend this idea to all update operations.
The resulting update semantics can be understood to _interleave_ calls to $f$ and $g$.
By doing so, these semantics can abandon the construction of paths altogether,
which results in higher performance when evaluating updates.

## Properties of path-less updates {#sec:update-props}

<!--
μονοπάτι = path
συνάρτηση = function
-->

Table: Properties of path-less update semantics. {#tab:update-props}

| $\varphi$ | $\varphi \update \sigma$ |
| --------- | ------------------------ |
| $\jqf{empty}$ | $.$ |
| $.$ | $\sigma$ |
| $f | g$ | $f \update (g \update \sigma)$ |
| $f, g$ | $(f \update \sigma) | (g \update \sigma)$ |
| $\jqite{\$x}{f}{g}$ | $\jqite{\$x}{f \update \sigma}{g \update \sigma}$ |
| $f \alt g$ | $\jqite{\jqf{first}(f \alt \jqf{false})}{f \update \sigma}{g \update \sigma}$ |

@tab:update-props gives a few properties that we want to hold for updates $\varphi \update \sigma$.
Let us discuss these for the different filters $\varphi$:

- $\jqf{empty}$: Returns the input unchanged.
- "$.$": Returns the output of the update filter $\sigma$ applied to the current input.
  Note that while jq only returns at most one output of $\sigma$,
  these semantics return an arbitrary number of outputs.
- $f | g$: Updates at $f$ with the update of $\sigma$ at $g$.
  This allows us to interpret
  $(.[] | .[]) \update \sigma$ in @ex:arr-update by
  $.[] \update (.[] \update \sigma)$, yielding the same output as in the example.
- $f, g$: Applies the update of $\sigma$ at $g$ to the output of the update of $\sigma$ at $f$.
  We have already seen this at the end of @sec:jq-updates.
- $\jqite{\$x}{f}{g}$: Applies $\sigma$ at $f$ if $\$x$ holds, else at $g$.
- $f \alt g$: Applies $\sigma$ at $f$ if $f$ yields some output whose boolean value (see @sec:value-ops) is not false, else applies $\sigma$ at $g$.
  Here, $\jqf{first}(f)$ is a filter that returns
  the first output of its argument $f$ if there is one, else the empty list.

While @tab:update-props allows us to define the behaviour of several filters
by reducing them to more primitive filters,
there are several filters $\varphi$ which cannot be defined this way.
We will therefore give the actual update semantics of $\varphi \update \sigma$ in @sec:new-semantics
by defining $\upd\, \sem \varphi\, \sigma\, v$, not
by translating $\varphi \update \sigma$ to equivalent filters.

<!--
## Limiting interactions {#sec:limiting-interactions}

To define $\upd\, \sem \varphi\, \sigma\, v$, we first have to understand
how to prevent unwanted interactions between $\varphi$ and $\sigma$.
In particular, we have to look at variable bindings.

We can bind variables in $\varphi$; that is, $\varphi$ can have the shape $f \jqas \$x | g$.
Here, the intent is that $g$ has access to $\$x$, whereas $\sigma$ does not!
This is to ensure compatibility with jq's original semantics,
which execute $\varphi$ and $\sigma$ independently,
so $\sigma$ should not be able to access variables bound in $\varphi$.

::: {.example}
  Consider the filter $0 \jqas \$x | \varphi \update \sigma$, where
  $\varphi$ is $(1 \jqas \$x | .[\$x])$ and $\sigma$ is $\$x$.
  This updates the input array at index $1$.
  If $\sigma$ had access to variables bound in $\varphi$,
  then the array element would be replaced by $1$,
  because the variable binding $0 \jqas \$x$ would be shadowed by $1 \jqas \$x$.
  However, in jq, $\sigma$ does not have access to variables bound in $\varphi$, so
  the array element is replaced by $0$, which is the value originally bound to $\$x$.
  Given the input array $[1, 2, 3]$, the filter yields the final result $[1, 0, 3]$.
:::

We take the following approach to prevent variables bound in $\varphi$ to "leak" into $\sigma$:
When evaluating $\varphi \update \sigma$, we want
$\sigma$ to always be executed with the same variable bindings.
In order to ensure that, we define
$\upd\, \sem \varphi\, \sigma\, v$ not for a _filter_ $\sigma$,
but for a _function_ $\sigma': \valt \to \listt$, where
$\sigma'\, x$ returns the output of the filter $\run\, \sigma\, x$.
This allows us to bind variables in $\varphi$ without impacting $\sigma$.
-->

## Path-less updates {#sec:new-semantics}

We will now give update semantics that define the output of
$\run\, \sem{f \update g}\, v$ as referred to in @sec:semantics.
We will first define
$$\run\, \sem{f \update g}\, v \coloneqq \upd\, \sem f\, \sigma\, v, \text{where }
  \sigma: \valt \to \stream{\resultt\, \valt} \coloneqq \run\, \sem g$$

Table: Path-less update semantics. Here, $\varphi$ is a filter and $\sigma: \valt \to \listt$ is a function from a value to a list of value results. {#tab:update-semantics}

| $\varphi$ | $\upd\, \sem \varphi\, \sigma\, v$ |
| --------- | ------------------------- |
| $.$ | $\sigma\, v$ |
| $..$ | $\upd \sem{\jqdef{r}{(.[]? | r), .} r}\, \sigma\, v$ |
| $f | g$ | $\upd\, \sem f\, (\upd\, \sem g\, \sigma)\, v$ |
| $f, g$ | $\upd\, \sem f\, \sigma\, v \bind \upd\, \sem g\, \sigma$ |
| $f \alt g$ | $\upd\, ((\run\, \sem f\, v \bind \trues)\, (\lambda \_\, \_. \sem f)\, \sem g)\, \sigma\, v$ |
| $.[p]^?$ | $\stream{v[p]^? \update \sigma}$ |
| $f \jqas \$x | g$ | $\reducef\, (\lambda x. (\lambda \$x. \upd\, \sem g)\, x\, \sigma)\, (\run\, \sem f\, v)\, v$ |
| $\jqite{\$x}{f}{g}$ | $\upd\, ((\bool\, \$x)\, \sem f\, \sem g)\, \sigma\, v$ |
| $\jqlb{break}{x}$ | $\stream{\breakf\, \$x}$ |
| $\jqfold{reduce}{f_x}{\$x}{(.; f)}$ | $\reducef_{\update}\, (\lambda \$x. \upd\, \sem f)\, \sigma\, (\run\, \sem{f_x}\, v)\, v$ |
| $\jqfold{foreach}{f_x}{\$x}{(.; f; g)}$ | $\foreachf_{\update}\, (\lambda \$x. \upd\, \sem f)\, (\lambda \$x. \upd\, \sem g)\, \sigma\, (\run\, \sem{f_x}\, v)\, v$ |
| $\jqdef{x(x_1; ...; x_n)}{f} g$ | $(\lambda x. \upd\, \sem g)\, (Y_{n+1}\, (\lambda x\, x_1\, ...\, x_n. \sem f))\, \sigma\, v$ |
| $x(f_1; ...; f_n)$ | $\upd\, (x\, \sem{f_1}\, ...\, \sem{f_n})\, \sigma\, v$ |

@tab:update-semantics shows the definition of $\upd\, \sem \varphi\, \sigma\, v$.
Several of the cases for $\varphi$, like
"$.$", "$f | g$", "$f, g$", and "$\jqite{\$x}{f}{g}$"
are simply relatively straightforward consequences of the properties in @tab:update-props.
We discuss the remaining cases for $\varphi$:

- "$..$": Update the input value and all recursively contained values.
  This is very similar to the evaluation of "$..$" in @tab:eval-semantics,
  but there, $r$ is defined as
  "$., (.[]? | r)$", whereas here, it is
  "$(.[]? | r), .$" --- the arguments of the concatenation are swapped.
  This leads values to be updated before the values that contain them.
  We discuss the effect of this in @ex:rec-update.
- $f \alt g$: Updates using $f$ if $f$ yields some non-false value, else updates using $g$.
  Here, we first call $f$ as a "probe".
  If it yields at least one output that is considered "true"
  (see @sec:semantics for the definition of $\trues$),
  then we update at $f$, else at $g$.
  This filter is unusual because is the only kind where a subexpression may be both
  evaluated ($\run\, \sem f\, v$) as well as
  updated with ($\upd\, \sem f\, \sigma\, v$).
- $.[p]^?$: Applies $\sigma$ to the current value at the path part $p$
  using the update operators in @sec:value-ops.
- $f \jqas \$x | g$:
  Folds over all outputs of $f$, using the input value $v$ as initial accumulator and
  updating the accumulator by $g \update \sigma$, where
  $\$x$ is bound to the current output of $f$.
  The definition of $\reducef$ is given in @sec:folding.
  <!-- TODO: explain that $x should not be bound in \sigma -->
- $\jqfold{\fold}{x}{\$x}{(.; f)}$: Folds $f$ over the values returned by $\$x$.
  We will discuss this in @sec:folding-update.
- $\jqdef{x(x_1; ...; x_n)}{f} g$: Defines a filter.
  This is defined analogously to @tab:eval-semantics.
- $x(f_1; ...; f_n)$, $x$: Calls a filter.
  This is defined analogously to @tab:eval-semantics.

<!-- TODO: make undefined filters explicit -->
There are many filters $\varphi$ for which
$\upd\, \sem \varphi\, \sigma\, v$ is not defined,
for example $\$x$, $[f]$, and $\{\}$.
In such cases, we assume that $\upd\, \sem \varphi\, \sigma\, v$ returns an error just like jq,
because these filters do not return paths to their input data.
Our update semantics support all kinds of filters $\varphi$ that are supported by jq, except for
$\jqlb{label}{x} | g$ and $\jqtc{f}{g}$.

::: {.example name="Update compilation"}
  Let us consider the jq filter $(.[] \update (.+.))$.
  When given an array as input, this filter outputs a new array where
  each value in the input array is replaced by the output of $.+.$ on the value.
  The filter $.+.$ returns the sum of the input and the input,
  effectively doubling its input.
  For example, when given the input $[1, 2, 3]$, the output of $\varphi$ is $[2, 4, 6]$.
  Before we can execute the jq filter, we have to lower it to IR, e.g. to
  $\varphi \equiv (.[] \update (. \jqas \$x | \$x + \$x))$.^[
    Note that the actual lowering $(.[] \update (. \jqas \$x | . \jqas \$y | \$x + \$y))$
    is a bit longer than the $\varphi$ given here, but
    because the two are semantically equivalent, we continue with $\varphi$.
  ]
  Let us now trace the execution of the filter, namely
  $\eval\, \sem \varphi\, v = (\lambda \fresh. \run\, \sem \varphi)\, \zero\, v$.
  Because $\varphi$ does not use any labels,
  this is equivalent to just $\run\, \sem \varphi\, v = \upd\, \sem{(.[])}\, \sigma\, v = (v[] \update \sigma)$.
  Here, we introduced $\sigma \equiv \run\, \sem{. \jqas \$x | \$x + \$x}$.
  We can further expand $\sigma$:
  \begin{align*} \sigma
  &= \lambda v. \run\, \sem{. \jqas \$x | \$x + \$x}\, v \\
  &= \lambda v. \run\, \sem{.} \bind (\lambda \$x. \run\, \sem{\$x + \$x}\, v) \\
  &= \lambda v. \stream{\ok v} \bind (\lambda \$x. \stream{\$x + \$x}) \\
  &= \lambda v. \stream{v + v}
  \end{align*}
  In summary, $\eval \sem \varphi v = (v[] \update (\lambda v. \stream{v + v}))$.
:::

::: {.example #ex:rec-update name="Recursive update"}
Consider the input $[1]$ and the filter $.. \update f$, where $f$ is $\{a: .\}$.
This filter is supposed to
replace all values $v$ recursively contained in the input
by the object $\{a: v\}$.

First, let us consider how *path-based* updates handle this.
The filter "$..$" is equivalent to $(\jqdef{r}{., (.[]? | r)} r)$ and
yields the paths
"$.$" (pointing to $[1]$) and
"$.[0]$" (pointing to $1$).
The path-based update thus returns the same as $(. \update f) | (.[0] \update f)$.
However, the result of "$. \update f$" is $\{a: [1]\}$,
for which the path "$.[0]$" is invalid --- the path-based update fails with an error.
The problem here is that "$..$" yields values closer to the root before values closer to the leaves.
We call this strategy "root-first", as opposed to "leaf-first".

Next, let us consider how path-less updates would evaluate
$.. \update f$ if "$..$" was interpreted like above.
This, again, performs updates root-first.
Using @tab:update-props, we can show that this is equivalent to
$\jqdef{r}{f | (.[]? \update r)} r$.
In this filter, it depends on the outputs of $f$ how often the update $r$ is performed;
for example, if $f$ always yields a non-empty array or object
(as is the case for our given $f$), then $r$ does not terminate.
This significantly diverges from the behaviour of path-based updates.

This is why we use a different way to interpret "$..$" on the left-hand side of updates, namely as
$\jqdef{r}{(.[]? | r), .} r$.
This performs updates leaf-first.
We can show that using this, $.. \update f$ is equivalent to
$\jqdef{r}{(.[]? \update r) | f} r$.
Here, the number of times $r$ calls $f$
does _not_ depend on the output of $f$, but only on the
original input given to $r$.
This matches the behaviour of path-based updates much more closely,
yet it terminates with a valid result, namely $\{a: [\{a: 1\}]\}$.
:::

::: {.example name="The Curious Case of Alternation"}
  The semantics of $(f \alt g) \update \sigma$ can be rather surprising:
  For the input
  $\obj{\jqstr{a} \mapsto \true}$, the filter
  $(.[\jqstr{a}] \alt .[\jqstr{b}]) \update 1$ yields
  $\obj{\jqstr{a} \mapsto 1}$.
  This is what we might expect, because the input has an entry for $\jqstr{a}$.
  Now let us evaluate the same filter on the input
  $\obj{\jqstr{a} \mapsto \false}$, which yields
  $\obj{\jqstr{a} \mapsto \false, \jqstr{b} \mapsto 1}$.
  Here, while the input still has an entry for $\jqstr{a}$ like above,
  its boolean value is _not_ true, so $.[\jqstr{b}] \update 1$ is executed.
  In the same spirit, for the input $\obj{}$ the filter yields $\obj{\jqstr{b} \mapsto 1}$,
  because $.[\jqstr{a}]$ yields $\nullf$ for the input,
  which also has the boolean value $\false$, therefore $.[\jqstr{b}] \update 1$ is executed.

  For the input
  $\obj{}$, the filter
  $(\false \alt .[\jqstr{b}]) \update 1$ yields
  $\obj{\jqstr{b} \mapsto 1}$.
  This is remarkable insofar as $\false$ is not a valid path expression
  because it returns a value that does not refer to any part of the original input,
  yet the filter does not return an error.
  This is because
  $\false$ triggers $.[\jqstr{b}] \update 1$, so
  $\false$ is never used as path expression.
  However, running the filter $(\true \alt .[\jqstr{b}]) \update 1$
  _does_ yield an error, because
  $\true$ triggers $\true \update 1$, and
  $\true$ is not a valid path expression.

  Finally, on the input
  $[]$, the filter
  $(.[] \alt \jqf{error}) \update 1$ yields
  $\stream{\err\, []}$.
  That is because $.[]$ does not yield any value for the input,
  so $\jqf{error} \update 1$ is executed, which yields an error.
:::

## Folding {#sec:folding-update}

In @sec:folding, we have seen how to evaluate folding filters of the shape
$\jqfold{reduce }{x}{\$x}{(.; f)}$ and
$\jqfold{foreach}{x}{\$x}{(.; f; g)}$.
Here, we will define path-less update semantics for these filters.
These update operations are _not_ supported in jq 1.8; however,
we will show that they arise quite naturally from previous definitions.

Let us start with an example to understand folding on the left-hand side of an update.

::: {.example #ex:folding-update}
  Let $v = [[[2], 1], 0]$ be our input value
  and $\varphi$ be the filter $\jqfold{\fold}{(0, 0)}{\$x}{(.; .[\$x])}$.
  The regular evaluation of $\varphi$ with the input value as described in @sec:semantics yields
  $$\run\, \sem \varphi\, v = \begin{cases}
    \stream{\phantom{[[2], 1],\,} [2]} & \text{if } \fold = \jqf{reduce} \\
    \stream{         [[2], 1],    [2]} & \text{if } \fold = \jqf{foreach}
  \end{cases}$$
  When $\fold = \jqf{foreach}$, the paths corresponding to the output are $.[0]$ and $.[0][0]$, and
  when $\fold = \jqf{reduce}$, the paths are just $.[0][0]$.
  Given that all outputs have corresponding paths, we can update over them.
  For example, taking $. + [3]$ as filter $\sigma$, we should obtain the output
  $$\upd\, \sem \varphi\, (\run\, \sem \sigma)\, v = \begin{cases}
    \stream{[[[2, 3], 1\phantom{, 3}], 0]} & \text{if } \fold = \jqf{reduce} \\
    \stream{[[[2, 3], 1         , 3 ], 0]} & \text{if } \fold = \jqf{foreach}
  \end{cases}$$
:::

First, note that for folding filters,
the lowering in @tab:lowering and
the defining equations in @sec:folding
only make use of filters for which we have already introduced update semantics in @tab:update-semantics.
This should not be taken for granted; for example, we originally lowered
$\jqfold{\fold}{f_x}{\$x}{(f_y; f)}$ to
$$\floor{f_y} \jqas \$y | \jqfold{\fold}{\floor{f_x}}{\$x}{(\$y; \floor{f})}$$
instead of the more complicated lowering found in @tab:lowering, namely
$$. \jqas \$x' | \floor{f_y} | \jqfold{\fold}{\floor{\$x' | f_x}}{\$x}{(.; \floor{f})}.$$
While both lowerings produce the same output for regular evaluation,
we cannot use the original lowering for updates, because the defining equations for
$\jqfold{\fold}{x}{\$x}{(\$y; f)}$ would have the shape $\$y | ...$,
which is undefined on the left-hand side of an update.
However, the lowering in @tab:lowering avoids this issue
by not binding the output of $f_y$ to a variable,
so it can be used on the left-hand side of updates.

To obtain an intuition about how the update evaluation of a fold looks like, we can take
$\jqfold{\fold}{x}{\$x}{(.; f; g)} \update \sigma$,
substitute the left-hand side by the defining equations in @sec:folding and
expand everything using the properties in @sec:update-props.
This yields
\begin{alignat*}{2}
\jqfold{reduce}{x}{\$x}{(.; f   )} \update \sigma
={}& x_0 \jqas \$x | (f \update ( \\
 & ... \\
 & x_n \jqas \$x | (f \update (  \\
 & \sigma))...)) \\
\jqfold{foreach}{x}{\$x}{(.; f; g)} \update \sigma
={}& x_0 \jqas \$x | (f \update ((g \update \sigma) | \\
 & ... \\
 & x_n \jqas \$x | (f \update ((g \update \sigma) | \\
 & .))...)).
\end{alignat*}

::: {.example}
  To see the effect of above equations, let us reconsider
  the input value and the filters from @ex:folding-update.
  Using some liberty to write $.[0]$ instead of $0 \jqas \$x | .[\$x]$, we have:
  $$\varphi \update \sigma = \begin{cases}
    .[0] \update \phantom{\sigma | (}.[0] \update \sigma   & \text{if } \fold = \jqf{reduce} \\
    .[0] \update          \sigma | ( .[0] \update \sigma)  & \text{if } \fold = \jqf{foreach}
  \end{cases}$$
:::

We will now formally define the functions used in @tab:update-semantics.
For this, we first introduce a function $\foldf_{\update}$,
as counterpart to the function $\foldf$ in @sec:folding.
\begin{align*}
\mathcal U\, T\, U&\coloneqq T \to (U \to \stream{\resultt\, U}) \to U \to \stream{\resultt\, U} \\
\foldf_{\update}&{}: \mathcal U\, T\, U \to (T \to U \to \stream{\resultt\, U}) \to (U \to \stream{\resultt\, U}) \to \stream{\resultt\, T} \to U \to \stream{\resultt\, U} \\
&\coloneqq \lambda f\, g\, n. Y_2\, (\lambda F\, l\, v. l\, (\lambda h\, t. f\, h\, (\lambda x. g\, h\, x \bind F\, t)\, v)\, (n\, v))
\end{align*}
Using this function, we can now define
\begin{alignat*}{4}
\reducef _{\update} &\coloneqq \lambda f\,     &&\sigma. \foldf_{\update}\, f\, (\lambda h\, v. \stream{\ok v})\, && \sigma \\
\foreachf_{\update} &\coloneqq \lambda f\, g\, &&\sigma. \foldf_{\update}\, f\, (\lambda h\, v. g\, h\, \sigma\, v)\, && (\lambda v. \stream{\ok v})
\end{alignat*}
The types of the functions are:
\begin{alignat*}{2}
\reducef _{\update}&{}: \mathcal U\, T\, U                        &&\to (U \to \stream{\resultt\, U}) \to \stream{\resultt\, T} \to U \to \stream{\resultt\, U} \\
\foreachf_{\update}&{}: \mathcal U\, T\, U \to \mathcal U\, T\, U &&\to (U \to \stream{\resultt\, U}) \to \stream{\resultt\, T} \to U \to \stream{\resultt\, U}
\end{alignat*}
