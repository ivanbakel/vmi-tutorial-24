# VMI Iris Tutorial '24

This is the Iris program verification tutorial for the VMI summer retreat 2024.

It is meant to show off the Iris proof mode and tactics for verifying properties of HeapLang programs.

## Installation

This folder is meant to work with VSCode.
To open, follow the following steps:
1. Open VSCode
2. Open the command palette (`F1` or `Ctrl+Shift+P`)
3. Run the command `>Dev Containers: Open Folder in Container`
4. Wait for it to finish (might take a few minutes)
5. That's it. To see whether it works, open `examples/basic.v` and press `Alt+ArrowDown` to step through the file

### Required Software

The procedure above spawns a local Docker container having all the right software.
In order for this to work, you need to have Docker installed and enabled.
On Windows, you also need WSL2.
If you use MacOS, you'll figure it out.

### Local Installation (Linux only)

1. Install Opam, following [this tutorial here](https://opam.ocaml.org/doc/Install.html).
2. Run the `install_local.sh` script
3. Run `eval $(opam env)`.
4. Run `coqide`. This should open Coq IDE, which allows you to work with the files.
