#!/bin/sh

cd "$(dirname "$0")"

columns=
for col in "$@"
do
    columns="$columns\"$col\","
done
if [ -n "$columns" ]; then
    projection="[ .[] | {$columns} ]"
else
    projection="."
fi

cols='["instance",
"solver",
"stime",
"sresult",
"rate-result",
"rate-time",
"rate-space",
"rate-solution",
"rate-verified",
"rate-reason-deletions",
"rate-reason-deletions-shrinking-trail",
"rate-RAT-introductions",
"rate-RUP-introductions",
"rate-d-result",
"rate-d-time",
"rate-d-space",
"rate-d-solution",
"rate-d-verified",
"rate-d-reason-deletions",
"gratgen-result",
"gratgen-time",
"gratgen-space",
"gratgen-solution",
"gratgen-verified",
"drat-trim-result",
"drat-trim-time",
"drat-trim-space",
"drat-trim-solution",
"drat-trim-verified"]
'


# cat results.json | jq '[.[] | select(.instance == "ae_rphp035_05")] | [.[].solvers[] | select(.solver == "smallsat@default")] | [.[].checkers[] | select(.checker == "rate")]' | jq '.[:100]'

exec jq '[.[]
| .instance as $instance
| .solvers[] | . as $solver
|
    {
    instance: $instance,
    solver: $solver.solver,
    stime: $solver.time,
    sresult: .solution
    } +
    # {
    #   "rate-reason-deletions": null,
    #   "rate-d-reason-deletions": null,
    # } +
    reduce .checkers[] as $checker ({}; . + {
        (($checker.checker)+"-result"): $checker.result,
        (($checker.checker)+"-time"): $checker.time,
        (($checker.checker)+"-space"): $checker.space,
        (($checker.checker)+"-solution"): $checker.solution,
        (($checker.checker)+"-verified"): $checker.verified
        } +
        reduce ($checker.stats | keys[]) as $key ({}; . + {
            ($checker.checker+"-"+($key | gsub(" "; "-")) ):$checker.stats[$key]
        })
    )
]
' \
    | jq "$projection" \
    | jq -r "$cols as \$cols
| map(. as \$row | \$cols | map(\$row[.])) as \$rows
| \$cols, \$rows[]
| join(\",\")
"
