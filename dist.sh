#!/bin/sh
# Create anonymised distribution.
find -type f -path "./jaq/*" \( -name "*ml" -o -name "*.jq*" -o -name "*.dj" \) -exec sed -i \
  -e 's/Michael Färber/Anonymous/g' \
  -e 's/michael.faerber/anonymous/g' \
  -e 's/gedenkt.at/anonymous.org/g' \
  -e 's/01mf02/anonymous/g' \{\} \;
tar --exclude-vcs-ignores --exclude-vcs --exclude="target" --exclude=".github" \
  --transform 's,^,jq-lang-spec/,' \
  -cjf jq-lang-spec.tar.bz2 eval/ ujq/ jaq/
