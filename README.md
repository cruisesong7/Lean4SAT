# leansat

This repository implements propagators for Ramsey theory in Lean, integrating with the CaDiCaL solver via `cadical-lean` for SAT-based enumeration. The project builds on Lean's reverse foreign function interface (reverse-FFI) and includes utilities for input processing, edge counting, and triangle counting.

### Project Structure

*   **`leansat/`**: Contains the Lean code implementing the propagators that interface with the SAT solver.
*   **`RamseyLemmas/`**: Contains the Lean formalizations of Ramsey theory concepts and related lemmas used by the propagators.
*   **`cadical-lean/`**: Submodule or directory containing the modified CaDiCaL solver and its Lean FFI bindings.
*   **`*.cpp` / `*.h`**: C++ code for examples (like `edge_counter.cpp`) and potentially interfacing code.
*   **`*.sh`**: Shell scripts for building (`build.sh`) and generating CNF files (`main.sh`).

### Installation and Setup

Follow these steps to set up the project:

**Part 1: Install Lean and Build Propagators**

1.  **Install Lean:**
    Install Lean 4 using the instructions from [here](https://github.com/leanprover/lean4).
    For most systems, you can use `elan` to manage Lean installations.
    Ensure Lean is correctly installed by running:
    ```bash
    lean --version
    ```

2.  **Build the Lean Project:**
    From the root of this repository, use `lake` (Lean's build system) to build the Lean part of the project, including the propagators:
    ```bash
    lake build
    ```

3.  **Run Build Script:**
    Execute the `build.sh` script. This script performs several crucial steps:
    *   Downloads and builds shared libraries for all Lean dependencies.
    *   Converts the static Lean library (`libLean.a`) into a shared library (`libLean.so`).
    *   Builds the main `leansat` Lean project again (ensuring linkage).
    *   Sets up environment variables (`LIBRARY_PATH`, `LD_LIBRARY_PATH`, `CPLUS_INCLUDE_PATH`) required for the C++ code to find and link against the Lean libraries.
    *   Compiles the example C++ programs (`edge_counter.cpp`, `degree_counter.cpp`) that demonstrate calling Lean functions from C++.
    ```bash
    ./build.sh
    ```

**Part 2: Compile `cadical-lean`**

1.  **Navigate to `cadical-lean`:**
    Change directory to the `cadical-lean` submodule or directory (assuming it's located at `./cadical-lean`):
    ```bash
    cd ./cadical-lean
    ```
    *(Note: Adjust the path if `cadical-lean` is located elsewhere)*

2.  **Build `cadical-lean`:**
    Follow the instructions in the `cadical-lean` directory (e.g., its own `README.md`) to compile the C++ code and the Lean FFI bindings. This typically involves commands like:
    ```bash
    # Example build commands - replace with actual commands for cadical-lean
    ./configure && make
    ```
    Ensure the necessary shared libraries or executables for `cadical-lean` are built successfully.

3.  **Return to Root Directory:**
    Navigate back to the root directory of the `leansat` project:
    ```bash
    cd ..
    ```

**Generating SAT Encodings**

The `main.sh` script is used to generate the SAT encodings (in CNF format) for specific Ramsey number problems.

*   **Usage:**
    ```bash
    ./main.sh [options] n p q
    ```
    Where `n` is the number of vertices, `p` is the clique size for color 1, and `q` is the clique size for color 2.

*   **Example (Base Encoding):**
    Generate the base encoding for R(6, 3) on 17 vertices (without additional constraints like degrees and edge counts, which are handled by the propagators):
    ```bash
    ./main.sh 17 6 3
    ```

*   **Options:**
    The script accepts various options to add constraints like vertex degrees, edge counts, and triangle counts *to the CNF file itself*. Use the `-h` or `--help` flag for a full list of options:
    ```bash
    ./main.sh --help
    ```
    The generated CNF file will be named based on the parameters used (e.g., `constraints_17_6_3_0_0_0_0_0` for the base encoding).

**Running the Solver**

1.  **Execute `cadical-lean`:**
    After generating a CNF file (typically using `main.sh`), you must specify the number of vertices (`n`) using the `--order` flag when calling `cadical-lean`.

    *   **Using Propagator Constraints:**
        To enable the Lean propagators for edge or degree counts, use the corresponding flags:
        *   `--strict-edge-bound <bound>`: Enforces a strict upper bound on the number of edges (literals assigned true).
        *   `--strict-degree-bound <bound>`: Enforces a strict upper bound on the maximum degree of any vertex.

    *   **Example (R(3,7) on 23 vertices with edge bound 100):**
        First, generate the base CNF:
        ```bash
        ./main.sh 17 6 3
        ```
        Then, run the solver with the edge bound constraint:
        ```bash
        ./cadical-lean/build/cadical-lean --order 17 --strict-edge-bound 97 constraints_17_6_3_0_0_0_0_0
        ```