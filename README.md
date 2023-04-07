# pybmc

## Dependencies

* [aigertool](https://github.com/arminbiere/aiger): Used to convert `aig` format to `aag` format. Put it in the same directory as `main.py` by execute `git clone https://github.com/arminbiere/aiger.git` here, and build it with `./configure.sh && make`. Without this tool will only support `aag` format.
## USAGE

* `python main.py --aag <path to config file> --k <number of bound>`: run the algorithm with the given aag format file and bound k

## Note

* `git checkout k-induction` to switch to the k-induction branch