# Paper correspondence

Specification: Gao–Ji–Liu, [arXiv:2609.18865v1](https://arxiv.org/abs/2609.18865v1),
including the appended Supplemental Material. Names below are in `QuantumBehaviors`
unless qualified otherwise. `Verification/Challenge.lean` states the public obligations;
`Verification/Solution.lean` supplies their proofs in a separate Lean environment.

The definition modules contain the original physical models, not surrogate sets chosen
from the desired answer. `Definitions.lean` fixes the four-input models, classical
locality, curve and finite-description predicates. Further definition modules specify
general scenarios, shared randomness, finite lifts, POVMs, NPA and almost quantum.

## Actual entry definitions

- `Definitions`: Input=Fin 4, binary outputs=Bool, Behavior=R^64; true denotes output 1 and false its complement; `curve`, `alpha`, `Allowed`, `Synchronous`, `witness`, physical probability predicates
- `Definitions`: `FiniteStrategy dA dB` has arbitrary complex PSD trace-one density and local binary POVMs; `Cq` existentially quantifies arbitrary finite local dimensions, `Cqa=closure Cq` in finite-coordinate Euclidean topology; `CommutingStrategy H` has a unit state and bounded orthogonal projections on a complete complex Hilbert space with cross-party commutation; `Cqc` existentially quantifies such spaces in the ambient Type universe
- `Scenarios.Definitions`: corresponding arbitrary finite input/output models; no same-party commutation required
- `Definitions`: `IsSemialgebraic` is a finite Boolean combination of real multivariate polynomial signs; `IsSemianalyticAt` requires finitely many functions analytic on an open neighborhood containing the point
- `Definitions`: `BellLocal` is a finite convex mixture of actual deterministic local responses
- `Dimension.Definitions`: arbitrary probability-space shared randomness with a.e. bounded local strategies and coordinate Bochner barycenters; measurable physical kernels have automatic integrability
- `NPA.Definitions` and `AlmostQuantum.Definitions`: genuine finite moment certificates and actual state-commuting projection models, described below

## Paper exits and exact assumptions

| Paper | Formal exit | Assumptions and conclusion |
|---|---|---|
| Theorem 1 | `theorem_one` | Unconditional conjunction: p2 Bell-local; exact slice and nonsemialgebraicity/nonsemianalyticity for each q/qa/qc |
| Corollary 2 / S12 | `corollary_two` | Any genuine semialgebraic R containing Cq contains the entire curve on some (β,2), 1<β<2 |
| S1 | `hilbert_spectral_reflection` | Arbitrary nonzero complete complex Hilbert space, two star projections, 0<z<2, z in spectrum; then 2-z in spectrum |
| S2 | `four_projections_allowed`, `four_indexed_projections_allowed` | Four actual projections sum to αI on nonzero Hilbert space, 1<α<2; α=2-2/m, m≥3 |
| S3 | `FiniteConstruction.exists_four_real_projections`, `FiniteConstruction.exists_four_hilbert_projections` | Explicit real symmetric projections at every m≥3 in exactly dimension m; no realization assumption |
| Full cited KRS | `finite_four_projection_iff_mem_sigmaFour`, `hilbert_four_projection_iff_mem_sigmaFour` | Exact full allowed scalar set for finite/arbitrary Hilbert witnesses |
| S4 | `Scenarios.lemma_S4 nA nB` | Actual binary Cqa⊆Cqc for every finite input count |
| S5 | `POVM.remark_S5`, `POVM.BinaryStrategy.toScenario_realizes` | Arbitrary-Hilbert cross-commuting binary POVM dilation preserves the entire table |
| S6 | `synchronous_zero_witness_projections` | Actual synchronous commuting realization and F=0 produce genuine scalar-sum projections on a nonzero closed subspace |
| S7 | `quantum_exact_membership`, `quantum_exact_slice` | Exact original model slice, all three models |
| S8 | `intermediate_not_semialgebraic` | Every Cq⊆C⊆Cqc is not semialgebraic |
| S9 | `intermediate_not_semianalytic` | Same inclusions imply failure at the explicitly Bell-local p2 |
| S10 | `allowed_iff_analytic_lift`, `allowed_iff_punctured_sine`, `punctured_sine_analytic` | Scope example: unbounded auxiliary analytic lift, and punctured equation on 1<α<2; no claimed analytic description at 2 |
| S11 | `quantum_no_finite_semialgebraic_lift`; `quantum_no_finite_sdp_lift`; `quantum_no_finite_complex_sdp_lift` | No finite-dimensional genuine polynomial-sign lift or finite affine real/complex SDP lift for any original model; stronger intermediate-set versions provided |
| S13 | `proposition_S13` | For every 1<α<2, full curve table is nonlocal but correlators have an explicit Bell-local realization |
| S14 | `Dimension.corollary_S14`; `Dimension.curve_finite_strategy_dimension_bound`; `Dimension.curve_shared_dimension_bound` | m≥3; denominator q=m/gcd(m,2) bounds each original local dimension below, q≤Dsr≤m, q≤D≤24m, both Θ((2-αm)^-1), arbitrary shared randomness |
| S15 | `Scenarios.theorem_S15 n t` | All three actual synchronous binary sectors semialgebraic iff n≤3, including n=0; `synchronous_models_eq_of_le_three`; actual dimension 444 suffices at n=3 |
| S16 | `Scenarios.larger_scenario_not_semialgebraic` | nA,nB≥4 and mA,mB≥2, each original model nonsemialgebraic |
| NPA prose | `NPA.finite_complex_sdp`, `finite_level_forbidden_tail`, `finite_level_strict`, `complete_hierarchy`, `forbidden_eventually_excluded`, `no_uniform_finite_level` | Every finite order is an actual SDP outer approximation strictly larger than Cqc; forbidden points individually excluded eventually but no fixed order resolves the whole near-classical tail |
| Almost-quantum prose | `AlmostQuantum.mem_iff_certificate`, `finite_complex_sdp`, `Strategy.physical`, `forbidden_tail`, `cqc_strict_subset` | Actual state-only commuting projection model is finite SDP/semialgebraic and has the forbidden near-classical tail |

## Assumption discharge and scope

The final endpoints do not assume spectral classification, quantum realization, exact slice,
closure containment, analytic obstruction, Tarski–Seidenberg, Russell's classification,
finite tensor realization, or NPA completeness. Their intermediate hypotheses are discharged
by actual constructions. The fixed ambient Hilbert-space universe is explicit in `Cqc`;
no finite-dimensional bound is imposed on that commuting model.

Historical Bell/MIP*=RE/undecidability comparisons are contextual citations, not new
paper theorem obligations. No quantitative NPA rate, noisy dimension bound or strictness
between every consecutive level is asserted. Source-equivalent alternate proofs and the
cited Russell overstatement are explained in provenance.md, preserving the needed claim.

## NPA

`NPA.Letter = Fin 4 ⊕ Fin 4` uses one binary projection per input; the other
outcome is its complement. `WordRel` is an inductively generated syntactic congruence
containing precisely idempotency and cross-party commutation (and equivalence/congruence
rules). It is not defined by quantifying over a quantum model or assuming completeness.
Reversal is the involution because letters are selfadjoint.

`NPA.level k` uses all literal words of length ≤ k+1. Thus k=0 is the first
positive standard order, usually Q1. Duplicate word rows are deliberately retained.
`ReducedWords.lean` proves that quotienting those rows by WordRel preserves PSD and
recovers every original matrix entry by pullback; this is equivalent finite feasibility
with the usual reduced word rows, not a different hierarchy.

Each certificate is a Hermitian complex PSD Gram matrix, normalized at the empty word,
satisfying every syntactic equality u* v = r* s among its entries and the complete observed
Born table. Probability nonnegativity is explicit. Normalization and nonsignaling are proved
from the equations. This follows the physical-behavior/strengthened-Q1 convention discussed
in 0803.4290v1 §3 (plain lowest-order PSD alone can permit negative table entries).
The finite affine SDP has one moment LMI, 64 one-by-one LMIs for observed nonnegativity,
and finitely many real and imaginary affine equalities. Real auxiliaries and coefficients
are unrestricted. Word relation tests select fixed equalities noncomputably; existence of
a finite SDP is claimed, not an executable complexity bound for its construction.

Actual commuting strategies give certificates by Gram matrices of word vectors.
For the converse at all orders, bounded finite Gram vectors are placed in an explicit
Hilbert ultralimit. Their limiting inner products retain normalization, every word relation
and the Born table. On their closed cyclic span, orthogonal projections onto left-letter
word spans act by left concatenation. The syntactic relations prove idempotency and
cross-commutation of these bounded operators on a dense span, then everywhere. This
constructs a genuine `CommutingStrategy`, proving `complete_hierarchy`.

Endpoints: `finite_complex_sdp`, `level_semialgebraic`, `cqc_subset_level`,
`level_antitone`, `finite_level_tail`, `finite_level_forbidden_tail`, `finite_level_strict`,
`complete_hierarchy`, `excluded_at_finite_level`, `excluded_at_all_higher`,
`forbidden_eventually_excluded`, `no_uniform_finite_level`.
There is no asserted strictness of each successive hierarchy inclusion or convergence rate.

## Almost quantum

`AlmostQuantum.Strategy` is the bipartite specialization of 1403.4621v1 Definition1:
orthogonal projections, a unit vector, and Ai Bj ψ = Bj Ai ψ only on that vector.
No global cross-commutation is imposed. All outcomes (including complements) satisfy
the on-vector condition; nonnegative, normalized, nonsignaling probabilities are proved.

The 25 events are identity, four Alice letters, four Bob letters, and sixteen pair words.
The finite certificate imposes exact Gram identities for each projection's event rows.
A genuine strategy yields the certificate; conversely columns of a PSD square root give
vectors, and orthogonal projections onto appropriate event-row spans construct the actual
strategy. `mem_iff_certificate` proves both directions, with no realization premise.
The explicit finite SDP has one 25×25 complex Hermitian LMI and 1250 real matrix-entry
auxiliaries, together with finite affine equalities. It yields the claimed near-classical
forbidden tail and strict containment of Cqc.
