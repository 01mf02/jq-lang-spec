`ujq` is a very small interpreter based on the formal specification of the jq language.
Its point is not to provide a full user-friendly, performant jq implementation.
Instead, it aims to provide an implementation that is as compact as possible.

To try `ujq`, you need GHC (tried with 9.4.8) and a Rust toolchain (>= 1.65).

First, you need to clone a recent version of jaq, because `ujq` uses jaq's parser:

    git clone https://github.com/01mf02/jaq

Next, you can run `ujq`, e.g. like this:

    ./ujq 'def recurse(f): def rec: ., (f | rec); rec; 0 | recurse(.+1)'

Internally, this hands the filter to jaq's parser, which produces an AST.
The Haskell part then takes this AST and performs all
steps described in the formal specification (lowering to IR and interpretation).

Restrictions:

- The interpreter is not optimised at all for performance.
- Reporting of parse errors is extremely minimalistic.
- Modules are not supported.
- `ujq` takes only a single argument, namely a filter to be executed.
  It runs this filter with the input value `null`.
  To run a filter with input from a file, you can use something like
  `./ujq "`cat foo.json`"' | .'`.
  However, unlike `jq`, this works only if there is a single JSON value in the input file.
  Furthermore, this also accepts certain non-JSON values, such as `{a: 1}`.

Further examples:

    ./ujq 'def a: 1; def b: 2; a + b'
    ./ujq 'if . then 0 elif . == . then 1 end'
    ./ujq 'reduce  (2, 3) as $x (1; .+$x)'
    ./ujq 'foreach (2, 3) as $x (1; .+$x)
    ./ujq 'foreach (2, 3) as $x (1; .+$x; [., $x])'
    ./ujq '{a: 1, b: 2}'
    ./ujq '[. == ., 1] + ["a", {}]'
    ./ujq '{("a", "b"): (1, 2)}'
