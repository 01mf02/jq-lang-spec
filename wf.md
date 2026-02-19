# Wellformedness

To be able to run a filter,
we wish that its compiled form is a closed lambda term.
We will now show under which conditions this is the case.

\newcommand{\ub}{\operatorname{ub}}
Informally, we say that a filter is _wellformed_ if all references to
named filters, variables, and labels were previously bound.
For example, the filter "$a, \$x$" is not wellformed because
neither $a$ nor $\$x$ was previously bound, but the filter
"$\jqdef{a}{1} 2 \jqas \$x | a, \$x$" is wellformed.

@tab:ub specifies the unbound symbols in a filter.
For this, it uses a set of symbol names $c$ that may contain
variables $\$v_x$,
labels $\$l_x$, and
filters $x^n$.

| $\varphi$ | $\ub\, \varphi\, c$ |
| --------- | ----------------- |
| $n$, $s$, $.$, $..$, $[]$, or $\{\}$ | $\emptyset$ |
| $\$x$, $-\$x$, or $\jqlb{break}{x}$ | $\{\$x\} \setminus c$ |
| $[f]$ | $\ub\, f\, c$ |
| $\{\$x: \$y\}$ or $\$x \cartesian \$y$ | $\ub\, \$x\, c \cup \ub\, \$y\, c$ |
| $f \star g$ or $\jqtc{f}{g}$ | $\ub\, f\, c \cup \ub\, g\, c$ |
| $.[p]^?$ | $\bigcup_{\$x \in p} \ub\, \$x\, c$ |
| $f \jqas \$x | g$ | $\ub\, f\, c \cup \ub\, g\, (c \cup \{\$x\})$ |
| $\jqlb{label}{x} | f$ | $\ub\, f\, (c \cup \{\$x\})$ |
| $\jqite{\$x}{f}{g}$ | $\ub\, \$x\, c \cup \ub\, f\, c \cup \ub\, g\, c$ |
| $\jqfold{\fold}{f_x}{\$x}{(.; f; g)}$ | $\ub\, f_x\, c \cup \ub\, f\, (c \cup \{\$x\}) \cup \ub\, g\, (c \cup \{\$x\})$ |
| $\jqdef{x^n(x_1; \dots; x_n)}{f} g$ | $\ub\, f\, (c \cup \{x^n\} \cup \bigcup_i \{x_i\}) \cup \ub\, g\, (c \cup \{x^n\})$ |
| $x^n(f_1; \dots; f_n)$ | $\{x^n\} \setminus c \cup \bigcup_i \ub\, f_i\, c$ |

Table: Unbound symbols of an IR filter $\varphi$ with respect to a context $c$. {#tab:ub}

When we have a set of builtin filters such as
$c = \{\jqf{error}^0, \jqf{path}^1\}$ (see @sec:builtin), then
a compiled filter $\varphi$ is wellformed with respect to these filters iff
$\ub\, \varphi\, c = \emptyset$.
