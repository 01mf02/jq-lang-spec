# Conclusion

We have shown syntax and semantics of
a large subset of the jq programming language.

We first defined a subset of jq's filter syntax and
a simpler subset (IR), and gave a lowering from concrete jq syntax to IR.
We then gave formal semantics based on IR, by specifying
how to compile a jq program to a lambda term.
We discussed two strategies to interpret updates, namely
path-based and path-less.
We showed in our evaluation that our semantics can be implemented
compactly (ujq) and efficiently (jaq), and that
path-less updates can yield significant performance gains over path-based updates.

We hope that our work is useful in several ways:
For jq users, it provides a succinct reference of the language core.
Our work should also benefit implementers of tools that process jq programs,
such as compilers, interpreters, or linters.
In particular, this specification should be sufficient to
implement the core of a jq compiler or interpreter.
