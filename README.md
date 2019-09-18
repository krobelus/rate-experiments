## Experiments for evaluating [`rate`]

- [Thesis containing the problem description](./thesis.pdf)
- The full data is in [results.json](./results.json)
  Based on that we generate:
  - [tables](./t)
  - [plots](./p)

The workflow is roughly `./deploy.sh` to copy to a target machine and then execute `./run-all.sh` there. 
The thesis, plots and tables are generated using `make`.

[`rate`]: <https://github.com/krobelus/rate>
