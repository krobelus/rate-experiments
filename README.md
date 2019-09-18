This repository contains my [thesis](./thesis.pdf) and the scripts I used
to run the experiments evaluating DRAT proof checker [`rate`].

The full data set with the results is in [results.json](./results.json)
Based on that we generate [tables](./t) and [plots](./p) and the thesis using `make`.

The workflow to run the experiments is roughly `./deploy.sh` to copy to a
remote machine; then execute `./run-all.sh` there.

[`rate`]: <https://github.com/krobelus/rate>
