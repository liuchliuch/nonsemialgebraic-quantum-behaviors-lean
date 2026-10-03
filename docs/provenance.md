# Sources and third-party code

The mathematical specification is *Quantum Behaviors Are Not Semialgebraic*,
Minbo Gao, Zhengfeng Ji, Chenghua Liu, arXiv:2609.18865v1, submitted
2026-09-16 16:04:20 UTC. It comprises the Letter and its appended supplement.
The source archive was fetched again on 2026-10-02; its digest matches the original pin.
The following digests identify the reference copies used during development;
PDFs and duplicate upstream Lean files are not shipped in this repository.

- [https://arxiv.org/src/2609.18865v1](https://arxiv.org/src/2609.18865v1), SHA-256 `9fd7172941f214ae92d21b66c92323d6dd1fdac5c068abd99bf7eb94e0f14166`.
- [https://arxiv.org/pdf/2609.18865v1](https://arxiv.org/pdf/2609.18865v1), SHA-256 `3548b3790c259aade9593ba00a00dd08090b71347ddba29418220768413a75d7`.
- [1905.06223v3](https://arxiv.org/pdf/1905.06223v3), SHA-256 `062a9d25757ae4ca88b3ffca2164d88cb4a1aa9d5cda411d39a5f6b1365163ce`.
- [1910.01696v2](https://arxiv.org/pdf/1910.01696v2), SHA-256 `1e605a130fb4f9e4e75f56120ee92373fb8f0e9de129024a94ed5e562ff80bf3`.
- [0803.4290v1](https://arxiv.org/pdf/0803.4290v1), SHA-256 `a50e5ff8d4b15e8590e78d19d3d22b1ab07accaa67c0478bd0283d6a040d3b18`.
- [1403.4621v1](https://arxiv.org/pdf/1403.4621v1), SHA-256 `6dd7c29264382447203fdd2cab9b13a8d8d476bcfa22a848ae29f020ed95e505`.

## Adapted Sturm proofs

`QuantumBehaviors/Projection/Vendored/{Sign,SturmChainDefs,SturmTheorem}.lean`
derive from [leanprover/hex-real-roots-mathlib](https://github.com/leanprover/hex-real-roots-mathlib/tree/53ce31466dc5ff520463249d470119c1e0006e22),
commit `53ce31466dc5ff520463249d470119c1e0006e22` (2026-09-12),
by Kim Morrison, copyright Lean FRO, LLC., Apache-2.0. Headers and license are retained.
The files were adapted to project import paths and Lean 4.29.0-rc6 syntax;
selected proof helpers are exposed for the weighted Sturm extension. The unavailable
newer polynomial-at-infinity lemma is replaced by a proved local argument.
`SimpleRealRoot.lean` was consulted but is not used or redistributed.

Real quantifier elimination is proved in `Projection/`, using root sampling,
signed remainder chains, weighted Sturm counts, finite sign determination and uniform
rational decision trees. `IsSemialgebraic.project` is a theorem, not an axiom or part of
the definition of semialgebraicity.

## Proof choices and a cited-source qualification

### Russell 1910.01696v2, Theorem 4.7 (pages 11–13)

The cited PDF identifies itself as arXiv:1910.01696v2, 6 November 2019.
SHA-256: `1e605a130fb4f9e4e75f56120ee92373fb8f0e9de129024a94ed5e562ff80bf3`.
Official version URL: https://arxiv.org/pdf/1910.01696v2

Theorem 4.7 starts on page 11. Its assumptions on the scalar parameters are only
`a,b ∈ ℝ`, both nonzero. The generator relations are
`[A,aB+bC]=[B,aA+C]=0` for three projections.
The statement claims the universal algebra is `ℂ^8 ⊕ M₂`, with a displayed
matrix parameter on page 12:

`t = (b² + 2a²b − a²b² − a²)/(4a²b)`.

The original TeX was re-fetched during the release review. Taking `a=1`, `b=1/10` satisfies the stated scalar assumptions but gives exactly
`t=−2`. Thus the displayed M₂ block cannot be an orthogonal projection (its
first diagonal entry would be negative). The source proof itself assumes
`t∈(0,1)` when considering an irreducible two-dimensional representation.
This check establishes an overstatement in the displayed uniform block
formula; it does not establish any defect in the main paper's S15 conclusion.

The formalization proves the required finite-dimensional conclusion directly, using
a twelve-vector spanning argument. The S15 tracial, variational, compact-convexity
and finite tensor-realization argument yields a uniform local dimension bound 444.
The source's stronger full isomorphism is not needed for Gao–Ji–Liu S15.

### Alternate constructions

- Spectral reflection is proved by an explicit algebraic resolvent
  identity instead of the source's approximate-eigenvector argument.
- S3 finite projections use a weighted index involution. Its fixed points
  encode the paper's singleton 0 and 1 blocks, preserving exact dimension m.

Both alternatives preserve the paper's theorem conclusions and assumptions.

- S14 treats mixed states directly on columns of the positive density square root.
  Their coefficient-matrix ranges replace a chosen Schmidt decomposition, preserve both
  original local dimensions and yield the same denominator bound. Arbitrary probability-space
  mixtures are handled by genuine almost-everywhere and Bochner-integral arguments.
- The finite-SDP consequence uses PSD iff a Gram factor exists and proved projection closure,
  instead of assuming the principal-minor criterion. Complex matrices use separate real and
  imaginary polynomial equations. All affine coefficients and auxiliaries remain unrestricted.

- S15 uses dense nondegenerate objectives and continuity of support functions, instead of
  assuming the degenerate-parameter cases of an irreducible-block classification. Its
  finite cyclic tensor realization is built from transported multiplication and a proved
  surjective polar-isometry normalization. Ordinary matrix coordinates give the final
  actual density/POVM strategy. No universal finite-C*-classification theorem is assumed.
