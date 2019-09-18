This repository contains my [thesis](./thesis.pdf) and the scripts I used
to run the experiments evaluating DRAT proof checker [`rate`].

The full data set with the results is in [results.json](./results.json)
Based on that you can use `make` to generate [tables](./t) and [plots](./p),
and a [poster](./poster/poster.pdf) in addition to the thesis.

The workflow to run the experiments is roughly `./deploy.sh` to copy to a
remote machine; then execute `./run-all.sh` there.

[`rate`]: <https://github.com/krobelus/rate>
