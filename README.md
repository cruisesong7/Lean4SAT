# leansat

This repository implements propagators for Ramsey theory in Lean, integrating with the PicoSAT solver for SAT-based enumeration. The project builds on Lean's reverse foreign function interface (reverse-FFI) and includes utilities for input processing, edge counting, and triangle counting.

### Installation and Setup
Follow these steps to set up the project:

1. Install Lean
  Install Lean 4 by the instructions from [here](https://github.com/leanprover/lean4).
  For most systems, you can use elan to manage Lean installations.
  Ensure Lean is correctly installed by running:
  ```lean --version```

2. Build PicoSAT
Navigate to the ./picosat directory and follow the instructions in its README.md to build the PicoSAT solver.
Ensure the PicoSAT executable is built and accessible.

3. Build the Project
From the root of the repository, use lake (Lean's build system) to build the project:
```lake build```

5. Generate Encodings and Call PicoSAT
The instructions to generate SAT encodings and invoke PicoSAT are defined in lakefile.lean. Use the lake command to execute the encoding and solver pipeline:

6. Output Storage
The solutions output by PicoSAT are processed and stored in the Ramseygood.lean file as Lean objects.

7. Code Structure
Input Processing: Located in Utils.lean, which handles file reading and preprocessing.
Propagators: Most propagator implementations, such as edge and triangle counting, are in CardinalityCounter.lean.
