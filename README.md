# Morley's Categoricity Theorem in Lean 4

[![Build](https://github.com/NoneMore/MorleyCategoricityTheorem/actions/workflows/build-project.yml/badge.svg)](https://github.com/NoneMore/MorleyCategoricityTheorem/actions/workflows/build-project.yml)
[![Blueprint](https://github.com/NoneMore/MorleyCategoricityTheorem/actions/workflows/blueprint.yml/badge.svg)](https://github.com/NoneMore/MorleyCategoricityTheorem/actions/workflows/blueprint.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](LICENSE)

This repository formalizes **Morley's categoricity theorem** in Lean 4 using
[Mathlib](https://github.com/leanprover-community/mathlib4). The project follows a
blueprint-driven workflow: the blueprint records the mathematical dependency structure, while the
compiled Lean declarations are the source of truth for what is currently formalized.

The project is under active development.

## Project links

- [Project homepage](https://NoneMore.github.io/MorleyCategoricityTheorem/)
- [Blueprint](https://NoneMore.github.io/MorleyCategoricityTheorem/blueprint/)
- [Blueprint PDF](https://NoneMore.github.io/MorleyCategoricityTheorem/blueprint.pdf)
- [Blueprint dependency graph](https://NoneMore.github.io/MorleyCategoricityTheorem/blueprint/dep_graph_document.html)
- [Generated API documentation](https://NoneMore.github.io/MorleyCategoricityTheorem/docs/)

## Getting started

Install Lean 4 using the
[Lean installation guide](https://leanprover-community.github.io/get_started.html), then clone the
repository:

```bash
git clone https://github.com/NoneMore/MorleyCategoricityTheorem.git
cd MorleyCategoricityTheorem
```

Fetching the Mathlib cache is recommended before the first build:

```bash
lake exe cache get
```

Build the project with:

```bash
lake build MorleyCategoricityTheorem
```

When modules are added, removed, or renamed, check that the root import file is synchronized:

```bash
lake exe mk_all --check
```

## Repository layout

- [`MorleyCategoricityTheorem/`](MorleyCategoricityTheorem) contains the Lean source files.
- [`MorleyCategoricityTheorem.lean`](MorleyCategoricityTheorem.lean) is the root import file.
- [`blueprint/`](blueprint) contains the formalization blueprint.
- [`home_page/`](home_page) contains the project homepage used alongside the generated blueprint
  and API documentation.
- [`references/`](references) contains supporting references used by the project.
- [`scripts/`](scripts) contains repository maintenance and project tooling.
- [`docs/plan/`](docs/plan/) contains active Lean/formalization infrastructure plans, with
  [`docs/plan/README.md`](docs/plan/README.md) documenting their planning lifecycle.

## Contributing

Contributions are welcome. Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) before opening a pull
request. In particular, keep changes focused, run the relevant validation commands, and update the
blueprint only when the pull request intentionally includes blueprint work.

For formalization work, the
[blueprint dependency graph](https://NoneMore.github.io/MorleyCategoricityTheorem/blueprint/dep_graph_document.html)
is a useful starting point for understanding dependencies between tasks.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
