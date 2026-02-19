`ujq` is a very small interpreter based on the formal specification of the jq language.
Its point is not to provide a full user-friendly, performant jq implementation.
Instead, it aims to provide an implementation that is as compact and close to the formal specification as possible.

## Running

To try `ujq`, you need GHC (tried with 9.4.8) and a Rust toolchain (>= 1.65).

Next, you can run `ujq`, e.g. like this:

    ./ujq 'def recurse(f): def rec: ., (f | rec); rec; 0 | recurse(.+1)'

(The first run will be a bit slow, because it compiles ujq and jaq's parser.)

Internally, this hands the filter to jaq's parser, which produces an AST.
The Haskell part then takes this AST and performs all
steps described in the formal specification (lowering to IR and interpretation).

## Restrictions

- The interpreter is not optimised at all for performance.
- Reporting of parse errors is extremely minimalistic.
- Modules are not supported.
- `ujq` takes only a single argument, namely a filter to be executed.
  It runs this filter with the input value `null`.
  To run a filter with input from a file, you can use something like
  `./ujq "$(cat foo.json)"' | .'`.
  However, unlike `jq`, this works only if there is a single JSON value in the input file.
  Furthermore, this also accepts certain non-JSON values, such as `{a: 1}`.

## Examples

For every filter `$F` among the following examples,
`./ujq $F` yields the same output as
`jq -nc $F` and
`jaq -nc $F`.

~~~
$ ./ujq 'def a: 1; def b: 2; a + b'
3
$ ./ujq 'if . then 0 elif . == . then 1 end'
1
$ ./ujq 'reduce  (2, 3) as $x (1; .+$x)'
6
$ ./ujq 'foreach (2, 3) as $x (1; .+$x)'
3
6
$ ./ujq 'foreach (2, 3) as $x (1; .+$x; [., $x])'
[3,2]
[6,3]
$ ./ujq '{a: 1, b: 2}'
{"a":1,"b":2}
$ ./ujq '[. == ., 1] + ["a", {}]'
[true,1,"a",{}]
$ ./ujq '{("a", "b"): (1, 2)}'
{"a":1}
{"a":2}
{"b":1}
{"b":2}
$ ./ujq '[[1, 2], 3] | .[0][1]'
2
$ ./ujq '[[1, 2], 3] | .[0][1] |= .*2'
[[1,4],3]
$ ./ujq '[0, {a: 1}, 2] as [$x, {a: $y}] | $x, $y'
0
1
$ ./ujq 'foreach ([1, "a"], [2, "b"]) as [$x, $y] (0; .+$x; [., $y])'
[1,"a"]
[3,"b"]
~~~
