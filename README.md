# sme-swp

Modulo scheduling ILP for e-graph extraction.

## Setup

```sh
python3 -m venv venv
./venv/bin/pip install pulp
brew install graphviz imagemagick    # for the side-by-side rendering
cargo build --release
```

## Running the test pipeline

```sh
./venv/bin/python3 src/ilp-modulo-sched.py <num_trials> [base_seed]
```

Each trial:
1. Generates a random cyclic digraph + machine model.
2. Solves it with the Python ILP.
3. Validates the Python schedule.
4. Dumps the same problem to a `.swp` file and shells out to the Rust binary.
5. Asserts the Rust II matches the Python II.
6. Renders the e-graph and Python digraph side by side for manual inspection in `test_artifacts`.

## `.swp` file format

```
R <number of resource kinds> <r0> <r1> ... <r{S-1}>
N <num_nodes>
<name> <cost> <resource_kind>
...
E <num_edges>
<src_idx> <dst_idx> <d> <delta>
...
```

### Examples

3-node chain on a single 1-wide resource:

```
R 1 1
N 3
N0 1 0
N1 1 0
N2 1 0
E 2
0 1 1 0
1 2 1 0
```

Two-op recurrence with a back-edge:

```
R 2 1 1
N 2
A 2 0
B 3 1
E 2
0 1 2 0
1 0 3 1
```

Self-loop:

```
R 1 1
N 1
N0 2 0
E 1
0 0 2 1
```

## Running a hand-written `.swp`

```sh
./target/release/sme-swp path/to/your.swp [dot_output_path]
```

Prints `RESULT_II=<n>` (CBC also writes solver chatter to stdout).

