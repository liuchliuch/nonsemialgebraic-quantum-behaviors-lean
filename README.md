# Quantum Behaviors Are Not Semialgebraic

Lean formalization of [Gao–Ji–Liu, arXiv:2609.18865v1](https://arxiv.org/abs/2609.18865v1),
including the Supplemental Material.

The central theorem gives an explicit polynomial curve whose intersection with each
of the finite-dimensional, closure, and commuting quantum behavior sets is exactly
`{2 - 2/m | m ≥ 3}`. It proves nonsemialgebraicity and failure of semianalyticity at
a classical accumulation point. The library also covers finite-lift obstructions,
exact dimension bounds, the synchronous three/four-input threshold, larger scenarios,
NPA completeness and finite-level obstructions, and almost-quantum consequences.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
bash scripts/verify.sh
```

The toolchain is Lean **4.29.0-rc6**. Mathlib and all transitive dependencies are pinned
in `lake-manifest.json`. No workspace-specific paths or prebuilt project proofs are needed.
`verify.sh` builds the library and paper proof bindings, checks the specification boundary,
and audits every project-owned declaration for unapproved transitive axioms.

## Review the mathematical claims

Start with [Verification/Challenge.lean](Verification/Challenge.lean): 32 explicit
paper obligations, importing the model definitions independently of their proofs.
[Verification/Solution.lean](Verification/Solution.lean) contains matching statements
and their proof bindings. The intentional `sorry` placeholders occur only in Challenge;
it is never imported by the proof library or Solution.

[Lean Comparator](https://github.com/leanprover/comparator) compares those two environments,
checks the axiom whitelist, and replays the exported proofs in the Lean kernel.
See [verification instructions](docs/verification.md) for setup, reproduction, and the
precise limits of the local macOS check.

The review boundary uses actual density matrices and POVMs, Euclidean closure,
bounded commuting projections, and finite polynomial/analytic sign descriptions.
The exact slice, quantum realization, Tarski–Seidenberg theorem and NPA completeness
are proved, not assumed.

## Repository guide

- `QuantumBehaviors.lean`: import the complete proof library.
- `QuantumBehaviors/Definitions.lean`: core mathematical definitions, independent of proofs.
- `QuantumBehaviors/Main.lean`: Theorem 1, Corollary 2 and the exact-slice obstructions.
- `QuantumBehaviors/{Dimension,Scenarios,SmallInputs,Projection,POVM,NPA,AlmostQuantum}/`: supporting constructions and consequences.
- `Verification/`: independent statement/proof environments and Comparator configuration.
- `scripts/`: reproducible source checks, build, axiom audit and Comparator setup.
- [Paper map](docs/paper-map.md): paper-to-Lean correspondence and conventions.
- [Provenance](docs/provenance.md): source versions, proof choices and adapted Sturm code.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the axiom audit.
Compilation and Comparator verify formal statements; the paper correspondence still
requires mathematical review of those statements and their definitions.

## License and citation

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE) for third-party attribution.
Please cite the [paper](https://arxiv.org/abs/2609.18865v1); citation metadata is in
[CITATION.cff](CITATION.cff).
