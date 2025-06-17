#!/bin/bash
# abort on error
set -e

ghc -dynamic -Wall -O Main.hs
echo "$1" | (cd jaq/jaq-core && cargo run -q --example parse) | ./Main
