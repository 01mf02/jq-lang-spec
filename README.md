# A formal specification of the jq language

This is an ongoing effort to create
a formal specification of the programming language provided by [`jq`].

A rendered version is available as
[PDF](https://github.com/01mf02/jq-lang-spec/releases/latest/download/spec.pdf) and
[HTML](https://github.com/01mf02/jq-lang-spec/releases/latest/download/spec.html).

Run `make spec.pdf` to generate a PDF version of the specification.
For this, `pandoc`, `dot2tex`, and a TeX distribution should be installed.
(I currently use `pandoc` 3.4 and `dot2tex` 2.11.3.)

For interactive regeneration: `ls | entr make spec.pdf`

[`jq`]: https://jqlang.github.io/jq/
