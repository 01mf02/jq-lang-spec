# Conclusion

We have shown formal syntax and semantics of
a large subset of the jq programming language.

On the syntax side, we first defined a subset of jq's filter syntax.
We then introduced a simpler subset (IR) in order to simplify the semantics later,
and gave a lowering from concrete jq syntax to IR.

On the semantics side, we gave formal semantics based on IR.
First, we defined values and basic operations on them.
Then, we used this to define the semantics of jq programs,
by specifying how to compile a jq program to a lambda term.
A large part of this was dedicated to the evaluation of updates:
In particular, we showed a new approach to evaluate updates.
This approach, unlike the approach implemented in jq,
does not depend on separating path building and updating, but interweaves them.
This allows update operations to cleanly handle multiple output values
in cases where this was not possible before.
Furthermore, in practice, this avoids creating temporary data to store paths,
thus improving performance.
This approach is also mostly compatible with the original jq behaviour,
yet it is unavoidable that it diverges in some corner cases.

Finally, we presented our implementation `jaq` of the new semantics and
showed that its performance is best-in-class for jq implementations.
Furthermore, we showed that indeed, the new update semantics yield
particularly large speed-ups, compared to other operations.

We hope that our work is useful in several ways:
For users of the jq programming language, it provides
a succinct reference that precisely documents the language.
Our work should also benefit implementers of tools that process jq programs,
such as compilers, interpreters, or linters.
In particular, this specification should be sufficient to
implement the core of a jq compiler or interpreter.
