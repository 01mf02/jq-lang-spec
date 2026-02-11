.results |
[.[].parameters | select(.jq == "jq") | .f] as $f |
($f | to_entries[]) as {key: $i, value: $f} |
[$i, (.[] | select(.parameters.f == $f).min * 1000 | round)] |
@tsv