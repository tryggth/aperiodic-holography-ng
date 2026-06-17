# SpectreNG

A Python and Lean 4 project.

## Project Structure
- **Lean 4**: A complete Lean 4 package managed by `lake`.
  - Configured version: `leanprover/lean4:v4.31.0` (defined in `lean-toolchain`).
  - Executable target: `spectreng` (defined in `lakefile.toml`, entrypoint is `Main.lean`).
  - Library target: `SpectreNG` (source files under `SpectreNG/`).
- **Python**: A local Python virtual environment (`.venv`) initialized with Python 3.11.2.

---

## Getting Started

### 1. Python Virtual Environment
To activate and use the Python virtual environment:
```bash
# Activate the environment
source .venv/bin/activate

# Upgrade packages or install dependencies
pip install --upgrade pip setuptools wheel
# pip install <package-name>
```

### 2. Lean 4 Development
Lean uses the local toolchain specified in the `lean-toolchain` file. `elan` will automatically resolve and use this version.

#### Build the Project
To compile the Lean executable and libraries:
```bash
lake build
```

#### Run the Executable
After building, run the compiled executable:
```bash
./.lake/build/bin/spectreng
```

#### Running Lean Commands
To run Lean commands manually, you can prepend `lake env` or run standard `elan` commands:
```bash
lake env lean Main.lean
```

---

## Editor Configuration
The repository includes `.vscode/settings.json` configuring VS Code to automatically pick up the virtual environment's Python interpreter. The Lean 4 VS Code extension will automatically detect the toolchain from `lean-toolchain`.