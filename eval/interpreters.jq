[.[].results | map(.min * 1000 | round)] |
to_entries[] |
[.key] + .value |
@tsv
