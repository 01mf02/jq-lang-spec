#import "common.typ": *

= Syntax <syntax>

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

== HIR <hir>

A _filter_ $f$ is defined by

$ f :=& n #or_ s #or_ . \
  #or_& (f) #or_ f? #or_ [f] #or_ {f: f, ..., f: f} #or_ f p^? ... p^? \
  #or_& f star f #or_ f cartesian f \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (f; f) #or_ var(x) \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& "if" f "then" f "else" f #or_ "try" f "catch" f \
  #or_& x #or_ x(f; ...; f)
$ where
$p$ is a path part of the shape $ p := [] #or_ [f] #or_ [f:] #or_ [:f] #or_ [f:f], $
$x$ is an identifier (such as "empty"),
$n$ is a number (such as $42$ or $3.14$), and
$s$ is a string (such as "Hello world!").
We use the superscript "$?$" to denote an optional presence of "?"; in particular,
$f p^?... p^?$ can be
$f p$, $f p?$,
$f p p$, $f p?#h(0pt) p$, $f p p?$, $f p?#h(0pt) p?$,
$f p p p$, and so on.
The potential instances of the operators $star$ and $cartesian$ are given in @tab:binops.
All operators $star$ and $cartesian$ are left-associative, except for
"$|$", "$=$", "$update$", and "$aritheq$".
A folding operation $fold$ is either "reduce" or "foreach".

#figure(
  table(
    columns: 3,
    [Name], [Symbol], [Operators],
    [Complex], $star$, ["$|$", ",", ("=", "$update$", "$aritheq$", "$alteq$"), "$alt$", "or", "and"],
    [Cartesian], $cartesian$, [($eq.quest$, $!=$), ($<$, $<=$, $>$, $>=$), $dot.circle$],
    [Arithmetic], $dot.circle$, [($+$, $-$), ($times$, $div$), $mod$],
  ),
  caption: [
    Binary operators, given in order of increasing precedence.
    Operators surrounded by parentheses have equal precedence.
  ],
) <tab:binops>

A _filter definition_ has the shape
"$f(x_1; ...; x_n) := g$".
Here, $f$ is an $n$-ary filter with _filter arguments_ $x_i$, where $g$ may refer to $x_i$.
For example, this allows us to define filters that produce the booleans,
by defining $"true()" := (0 = 0)$ and $"false()" := (0 != 0)$.

// TODO: these must also hold for the main filter!
We are assuming a few preconditions that must be fulfilled for a filter to be well-formed.
For this, we consider a definition $x(x_1; ...; x_n) := phi$:

- Arguments must be bound:
  The only filter arguments that $phi$ can refer to are $x_1, ..., x_n$.
- Labels must be bound:
  If $phi$ contains a statement $"break" var(x)$,
  then it must occur as a subterm of $g$, where
  $"label" var(x) | g$
  is a subterm of $phi$.
- Variables must be bound:
  If $phi$ contains any occurrence of a variable $var(x)$,
  then it must occur as a subterm of $g$, where either
  $f "as" var(x) | g$ or
  $fold x "as" var(x) (y; g)$
  is a subterms of $phi$.


== MIR <mir>

We are now going to identify a subset of HIR called MIR and
show how to _lower_ a HIR filter to a semantically equivalent MIR filter.

A MIR filter $f$ has the shape
$ f :=& n #or_ s #or_ . \
  #or_& [f] #or_ {} #or_ {f: f} #or_ .p \
  #or_& f star f #or_ var(x) cartesian var(x) \
  #or_& f "as" var(x) | f #or_  fold f "as" var(x) (.; f) #or_ var(x) \
  #or_& "if" var(x) "then" f "else" f #or_ "try" f "catch" f \
  #or_& "label" var(x) | f #or_ "break" var(x) \
  #or_& x #or_ x(f; ...; f)
$
where $p$ is a path part of the shape
$ p := [] #or_ [var(x)] #or_ [var(x):var(x)]. $
Furthermore, the set of complex operators $star$ in MIR
does not include "$=$" and "$aritheq$" anymore.

Compared to HIR, MIR filters
have significantly simpler path operations
($.p$ versus $f p^?... p^?$) and
replace certain occurrences of filters by variables
(e.g. $var(x) cartesian var(x)$ versus $f cartesian f$).

#figure(caption: [Lowering of a	HIR filter $phi$ to a MIR filter $floor(phi)$.], table(columns: 2,
  $phi$, $floor(phi)$,
  [$n$, $s$, $.$, $var(x)$, or $"break" var(x)$], $phi$,
  $(f)$, $floor(f)$,
  $f?$, $"try" floor(f) "catch" "empty"()$,
  $[]$, $["empty"()]$,
  $[f]$, $[floor(f)]$,
  ${}$, ${}$,
  ${f: g}$, $floor(f) "as" var(x') | floor(g) "as" var(y') | {var(x'): var(y')}$,
  ${f_1: g_1, ..., f_n: g_n}$, $floor(sum_i {f_i: g_i})$,
  $f p_1^? ... p_n^?$, $. "as" var(x') | floor(f) | floor(p_1^?)_var(x') | ... | floor(p_n^?)_var(x')$,
  $f = g$, $floor(g) "as" var(x') | floor(f update var(x'))$,
  $f aritheq g$, $floor(f update . arith g)$,
  $f alteq g$, $floor(f update . alt g)$,
  $f "and" g$, $floor(f) "as" var(x') | var(x') "and" floor(g)$,
  $f "or"  g$, $floor(f) "as" var(x') | var(x') "or"  floor(g)$,
  $f star g$, $floor(f) star floor(g)$,
  $f cartesian g$, $floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
  $f "as" var(x) | g$, $floor(f) "as" var(x) | floor(g)$,
  $fold f_x "as" var(x) (f_y; f)$, $. "as" var(x') | floor(f_y) | fold floor(var(x') | f_x) "as" var(x) (.; floor(f))$,
  $"if" f_x "then" f "else" g$, $floor(f_x) "as" var(x') | "if" var(x') "then" floor(f) "else" floor(g)$,
  $"try" f "catch" g$, $"try" floor(f) "catch" floor(g)$,
  $"label" var(x) | f$, $"label" var(x) | floor(f)$,
  $x$, $x$,
  $x(f_1; ...; f_n)$, $x(floor(f_1); ...; floor(f_n))$,
)) <tab:lowering>

@tab:lowering shows how to lower an HIR filter $phi$ to
a semantically equivalent MIR filter $floor(phi)$.
In particular, this desugars path operations and
makes it explicit which operations are Cartesian or complex.
By convention, we write $var(x')$ to denote a fresh variable.
Notice that for some complex operators $star$, namely
"$=$", "$aritheq$", "$alteq$", "$"and"$", and "$"or"$",
@tab:lowering specifies individual lowerings, whereas
for the remaining complex operators $star$, namely
"$|$", "$,$", "$update$", and "$alt$",
@tab:lowering specifies a uniform lowering $floor(f star g) = floor(f) star floor(g)$.

#figure(caption: [Lowering of a path part $p^?$ with input $var(x)$ to a MIR filter.], table(columns: 2, align: left,
  $p    ^?$, $floor(p^?)_var(x)$,
  $[   ]^?$, $.[]^?$,
  $[f  ]^?$, $(var(x) | floor(f)) "as" var(y') | .[var(y')]^?$,
  $[f: ]^?$, $(var(x) | floor(f)) "as" var(y') | "length"()^? "as" var(z') | .[var(y') : var(z')]^?$,
  $[ :f]^?$, $(var(x) | floor(f)) "as" var(y') | 0 "as" var(z') | .[var(z') : var(y')]^?$,
  $[f:g]^?$, $(var(x) | floor(f)) "as" var(y') | (var(x) | floor(g)) "as" var(z') | .[var(y') : var(z')]^?$,
)) <tab:lower-path>

@tab:lower-path shows how to lower a path part $p^?$ to MIR filters.
Like in @hir, the meaning of superscript "$?$" is an optional presence of "$?$".
In the lowering of $f p_1^? ... p_n^?$ in @tab:lowering,
if $p_i$ in the first column is directly followed by "?", then
$floor(p_i^?)_var(x)$ in the second column stands for
$floor(p_i ?#h(0pt))_var(x)$, otherwise for
$floor(p_i  )_var(x)$.
Similarly, in @tab:lower-path, if $p$ in the first column is followed by "$?$", then
all occurrences of superscript "?" in the second column stand for "?", otherwise for nothing.

#example[
  The HIR filter $(.[]?#h(0pt) [])$ is lowered to
  $(. "as" var(x') | . | .[]? | .[])$.
  Semantically, we will see that this is equivalent to $(.[]? | .[])$.
]

#example[
  The HIR filter $mu eq.triple .[0]$ is lowered to
  $floor(mu) eq.triple . "as" var(x) | . | (var(x) | 0) "as" var(y) | .[var(y)]$.
  Semantically, we will see that $floor(mu)$ is equivalent to $0 "as" var(y) | .[var(y)]$.
  The HIR filter $phi eq.triple [3] | .[0] = ("length"(), 2)$ is lowered to the MIR filter
  $floor(phi) eq.triple [3] | ("length"(), 2) "as" var(z) | floor(mu) update var(z)$.
  In @semantics, we will see that its output is $stream([1], [2])$.
]

This lowering assumes the presence of one filter in the definitions, namely $"empty"$.
This filter returns an empty stream.
We might be tempted to define it as ${} | .[]$,
which constructs an empty object, then returns its contained values,
which corresponds to an empty stream as well.
However, such a definition relies on the temporary construction of new values
(such as the empty object here),
which is not admissible on the left-hand side of updates (see @updates).
For this reason, we have to define it in a more complicated way, for example
$ "empty"() := ({} | .[]) "as" var(x) | . $
This definition ensures that $"empty"$ can be employed also as a path expression.

The lowering in @tab:lowering is compatible with the semantics of the jq implementation,
with one notable exception:
In jq, Cartesian operations $f cartesian g$ would be lowered to
$floor(g) "as" var(y') | floor(f) "as" var(x') | var(x) cartesian var(y)$, whereas we lower it to
$floor(f) "as" var(x') | floor(g) "as" var(y') | var(x) cartesian var(y)$,
thus inverting the binding order.
Note that the difference only shows when both $f$ and $g$ return multiple values.
We diverge here from jq to make the lowering of Cartesian operations
consistent with that of other operators, such as ${f: g}$, where
the leftmost filter ($f$) is bound first and the rightmost filter ($g$) is bound last.
That also makes it easier to describe other filters, such as
${f_1: g_1, ..., f_n: g_n}$, which we can lower to
$floor(sum_i {f_i: g_i})$, whereas its lowering assuming the jq lowering of Cartesian operations would be
$floor({f_1: g_1}) "as" var(x'_1) | ... | floor({f_n: g_n}) "as" var(x'_n) | sum_i var(x'_i)$.

#example[
  The filter $(0, 2) + (0, 1)$ yields
  $stream(0, 1, 2, 3)$ using our lowering, and
  $stream(0, 2, 1, 3)$ in jq.
]

== Concrete jq syntax <jq-syntax>

Let us now go a level above HIR, namely a subset of actual jq syntax#footnote[
  Actual jq syntax has a few more constructions to offer, including
  nested definitions, variable arguments, string interpolation, modules, etc.
  However, these constructions can be transformed into
  semantically equivalent syntax as treated in this text.
] of which we have seen examples in @tour, and
show how to transform jq programs to HIR and to MIR.

A _program_ is a (possibly empty) sequence of definitions, followed by
a _main filter_ `f`.
A _definition_ has the shape `def x(x1; ...; xn): g;` or `def x: g`; where
`x` is an identifier,
`x1` to `xn` is a non-empty sequence of semicolon-separated identifiers, and
`g` is a filter.
In HIR, we write the corresponding definition as $x(x_1; ...; x_n) := g$.

The syntax of filters in concrete jq syntax is nearly the same as in HIR.
To translate between the operators in @tab:binops, see @tab:op-correspondence.
The arithmetic update operators in jq, namely
`+=`,
`-=`,
`*=`,
`/=`, and
`%=`,
correspond to the operators $aritheq$ in HIR, namely
$+#h(0pt)=$,
$-#h(0pt)=$,
$times#h(0pt)=$,
$div#h(0pt)=$, and
$mod#h(0pt)=$.
Filters of the shape
`if f then g else h end` correspond to the filter
$"if" f "then" g "else" h$ in HIR;
that is, in HIR, the final `end` is omitted.

In jq, it is invalid syntax to
call a nullary filter as `x()` instead of `x`, or to
define a nullary filter as `def x(): f;` instead of `def x: f;`.
On the other hand, on the right-hand side of a definition, `x` may refer either to
a filter argument `x` or a nullary filter `x`.
To ease our lives when defining the semantics, we allow the syntax $x()$ in HIR.
We unambiguously interpret $x$ as call to a filter argument and
$x()$ as call to a filter that was defined as $x() := f$.

#let correspondence = (
  (`|`, $|$),
  (`,`, $,$),
  (  `=`, $=$),
  ( `|=`, $update$),
  (`//=`, $alteq$),
  (`//`, $alt$),
  (`==`, $eq.quest$),
  (`!=`, $!=$),
  (`<` , $< $),
  (`<=`, $<=$),
  (`>` , $> $),
  (`>=`, $>=$),
  (`+`, $+$),
  (`-`, $-$),
  (`*`, $times$),
  (`/`, $div$),
  (`%`, $mod$),
)
#figure(caption: [Operators in concrete jq syntax and their corresponding HIR operators.], table(columns: 1+correspondence.len(),
  [jq],  ..correspondence.map(c => c.at(0)),
  [HIR], ..correspondence.map(c => c.at(1)),
)) <tab:op-correspondence>

To convert a jq program to MIR, we do the following:

+ For each definition, convert it to a HIR definition.
+ Convert the main filter `f` to a HIR filter $f$.
+ Replace the right-hand sides of HIR definitions and $f$ by
  their lowered MIR counterparts, using @tab:lowering.

#example[
  Consider the jq program `def recurse(f): ., (f | recurse(f)); recurse(. + 1)`,
  which returns the infinite stream of output values $n, n+1, ...$
  when provided with an input number $n$.
  The definition in this example can be converted to the HIR definition
  $"recurse"(f) := ., (f | "recurse"(f))$ and the main filter can be converted to the HIR filter
  $"recurse"(. + 1)$.
  The lowering of the definition to MIR yields the same as the HIR definition, and
  the lowering of the main filter to MIR yields
  $"recurse"(. "as" var(x') | 1 "as" var(y') | var(x') + var(y'))$.
]

#example[
  Consider the jq program `def select(f): if f then . else empty end; def negative: . < 0; .[] | select(negative)`.
  When given an array as an input, it yields
  those elements of the array that are smaller than $0$.
  Here, the definitions in the example are converted to the HIR definitions
  $"select"(f) := "if" f "then" . "else" "empty"()$ and
  $"negative"() := . < 0$, and
  the main filter is converted to the HIR filter
  $.[] | "select"("negative"())$.
  Both the definition of $"select"(f)$ and the main filter are already in MIR;
  the MIR version of the remaining definition is
  $"negative"() := . "as" var(x') | 0 "as" var(y') | var(x') < var(y')$.
]

We will show in @semantics how to run the resulting MIR filter $f$
in the presence of a set of MIR definitions.
For a given input value $v$, the output of $f$ will be given by $f|^{}_v$.
