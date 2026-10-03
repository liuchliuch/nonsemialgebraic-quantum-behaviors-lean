# Verification

## Reproduce the source check

```sh
lake exe cache get
bash scripts/verify.sh
lake build Verification.Challenge
```

`verify.sh` checks that every proof module is reachable from the library entrypoint,
that the challenge imports only the documented specification boundary, that all 32
source signatures match their proof bindings and Comparator configuration, and that
production Lean source contains no proof holes or project axioms. It then builds
all proofs and traverses the transitive axioms of **every** project-owned declaration,
including private/generated names, adapted Sturm lemmas and `Verification.Solution`.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The audit also checks
membership in Lean's checked kernel environment. Its generated declaration list is
written to `.verification/axiom-roots.tsv`, which is not committed.

For a fresh project rebuild, remove `.lake/build` and repeat these commands. This
retains only dependency caches. `lake clean` also works, but may clean dependencies.
If the optional ProofWidgets release download fails, use
`lake exe cache get --skip-proofwidgets` and obtain its assets separately if needed.

The fixed Lean elaboration setting `backward.isDefEq.respectTransparency=false`
is configured in Lake and the audit command to reproduce the original proof sources.
It affects elaboration, not the logical axiom whitelist. Do not upgrade the pinned
compiler or Mathlib as part of reproduction.

## Independent specification and Comparator

`Verification/Challenge.lean` contains the reviewed statements with intentional proof
placeholders. `Verification/Solution.lean` states the same obligations and supplies
proofs from the library. They define the same `PaperChecks` names in **separate**
environments and must not be imported together. Neither Solution nor the production
library imports Challenge.

The challenge's project imports are restricted to the seven definition modules and
`NPA/Words.lean`. The latter adds finite word indexing and elementary syntactic lemmas;
it does not import containment, completeness or the paper's conclusions. The core
`effect` simplification lemmas are reflexive equations. All mathematical model and
finite-description definitions must be reviewed as part of the specification.

Use the [official Comparator](https://github.com/leanprover/comparator/tree/a4f696825c583ed8a5b4060d9a0faa5b882d365b)
at the toolchain-matched revision, with its pinned exporter and checker dependencies:

```sh
bash scripts/setup-comparator.sh
go install github.com/zouuup/landrun/cmd/landrun@v0.1.14  # Linux; requires Go
export PATH="$(go env GOPATH)/bin:$PATH"
bash scripts/compare.sh
```

For a trusted local checkout on macOS, use the explicit development mode:

```sh
bash scripts/setup-comparator.sh
bash scripts/compare.sh --local
```

The setup script pins Comparator commit `a4f696825c583ed8a5b4060d9a0faa5b882d365b`
(tag `v4.29.0-rc6`). Its upstream lockfile pins lean4export to
`048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` and Lean4Checker to
`b7398199245524275543dec6113229c9bb4902e5`. The project configuration compares all 32
obligations and permits only the three standard axioms. It does not enable nanoda.
`COMPARATOR_HOME` can select an already-built checkout at that revision.

Comparator compares declaration types **and their defining dependencies**, rejects
unapproved axioms in the proofs, and replays the exported solution through Lean's
kernel. This is stronger than matching printed theorem names or merely running a
source search for `sorry`. It does not determine whether the specification correctly
expresses the informal paper.

Real [landrun](https://github.com/Zouuup/landrun) supplies the Linux sandbox.
The explicit `--local` option supplies a temporary development runner without a
sandbox. A successful macOS replay
therefore verifies statement equality, axioms and kernel acceptance; it does **not**
certify process isolation against adversarial build code. The local review used a
development runner. No external independent kernel was run.

## Recorded review

Release checks completed on **2026-10-02 (Asia/Shanghai)**:

| Check | Result |
|---|---|
| Standard Lake build | Passed; 141 library modules and the Solution module |
| Global transitive axiom audit | Passed; 2,612 owned declarations, exactly the permitted standard axioms |
| Independent Challenge elaboration | Passed; 32 intentional specification placeholders |
| Official Comparator | Passed all 32 obligations; exit code 0; Lean kernel accepted the exported solution |
| Process isolation | macOS development shim; no sandbox and no additional independent kernel |
| GitHub Actions | Configured; no remote run was performed during the local review |

The original 133 supporting proof modules are all retained. Extracting definitions
preserved their content; the extra 32 owned declarations are precisely the public
proof bindings. The release source contains 161 files (down from 309); generated
build products and local logs are excluded by `.gitignore`.


The original 134-module source tree passed a fresh standard Lake build on 2026-10-02.
Its global audit checked 2,580 project-owned declarations with only the permitted
standard axioms. The original Linux-workspace scripts were not used.

The release review re-fetched the versioned arXiv TeX archive and checked its digest,
read the Letter and supplement, compared model definitions and every numbered exit,
and inspected the load-bearing spectral, cyclic-subspace, realization, closure,
dimension, small-input and relaxation constructions. No change to the paper's main
mathematical claims was required. Definitions were extracted without changing their
content; public claims were restated as independent Comparator obligations.

This is a source review and machine verification, not an independent
human certification. Linter suggestions in the inherited proofs do not invalidate
successful kernel checks. The GitHub workflow builds, audits and elaborates the
specification and runs Comparator with landrun on Linux; local success does not mean that a remote GitHub run has occurred.

## Release recheck on 2026-10-04

The standard Lake build, source checks, and transitive axiom audit were rerun
successfully in a separate local workspace, using the pinned toolchain and
previously compiled caches. Comparator passed all 32 obligations and Lean
kernel replay in macOS development mode without process sandboxing.

All Lean source files are byte-for-byte unchanged from the 2 October source
distribution. Release edits are limited to packaging exclusions, documentation,
and the explicit local Comparator development runner. Source checks, archive integrity, script syntax,
configuration formats, and local documentation links were checked again.
