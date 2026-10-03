import QuantumBehaviors

/-! Proof bindings for the independently stated paper specification in Challenge.lean. -/

open QuantumBehaviors Set Filter Asymptotics
open scoped BigOperators

namespace PaperChecks

theorem theorem_one :
    BellLocal (curve 2) ∧ ∀ t : Model,
    {α : ℝ | α ∈ Ioo (1 : ℝ) 2 ∧ curve α ∈ quantumSet t} = {α | Allowed α} ∧
    ¬ IsSemialgebraic (quantumSet t) ∧ ¬ IsSemianalyticAt (quantumSet t) (curve 2) :=
  QuantumBehaviors.theorem_one

theorem corollary_two :
    ∀ (R : Set Behavior), IsSemialgebraic R → Cq ⊆ R →
    ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, curve α ∈ R :=
  fun _ => QuantumBehaviors.corollary_two

theorem lemma_S1 :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (P Q : H →L[ℂ] H),
    IsStarProjection P → IsStarProjection Q → ∀ z : ℝ, 0 < z → z < 2 →
    (z : ℂ) ∈ spectrum ℂ (P + Q) → ((2 - z : ℝ) : ℂ) ∈ spectrum ℂ (P + Q) :=
  fun _ _ _ _ _ _ _ hP hQ _ => QuantumBehaviors.hilbert_spectral_reflection hP hQ

theorem proposition_S2 :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (P : Input → H →L[ℂ] H),
    (∀ i, IsStarProjection (P i)) → ∀ α : ℝ,
    (∑ i, P i) = algebraMap ℝ (H →L[ℂ] H) α → 1 < α → α < 2 → Allowed α :=
  fun _ _ _ _ _ P hP _ => QuantumBehaviors.four_indexed_projections_allowed P hP

theorem proposition_S3 :
    ∀ m : ℕ, 3 ≤ m → ∃ P : Input → Matrix (Fin m) (Fin m) ℝ,
    (∀ i, (P i).transpose = P i) ∧ (∀ i, P i * P i = P i) ∧
    (∑ i, P i) = alpha m • (1 : Matrix (Fin m) (Fin m) ℝ) :=
  QuantumBehaviors.FiniteConstruction.exists_four_real_projections

theorem lemma_S4 :
    ∀ nA nB : ℕ, Scenarios.Cqa nA nB 2 2 ⊆ Scenarios.Cqc nA nB 2 2 :=
  QuantumBehaviors.Scenarios.lemma_S4

theorem remark_S5 :
    POVM.CqcPOVM = Cqc :=
  QuantumBehaviors.POVM.remark_S5

theorem lemma_S6 :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (s : CommutingStrategy H) (p : Behavior),
    s.realizes p → Synchronous p → ∀ α : ℝ, witness p α = 0 →
    ∃ (K : Submodule ℂ H) (_ : CompleteSpace K) (_ : Nontrivial K)
      (P : Input → K →L[ℂ] K), (∀ i, IsStarProjection (P i)) ∧
      (∑ i, P i) = algebraMap ℝ (K →L[ℂ] K) α :=
  fun _ _ _ _ s _ hp hs _ => QuantumBehaviors.synchronous_zero_witness_projections s hp hs

theorem theorem_S7 :
    ∀ (t : Model) (α : ℝ), 1 < α → α < 2 →
    (curve α ∈ quantumSet t ↔ Allowed α) :=
  fun t _ => QuantumBehaviors.quantum_exact_membership t

theorem corollary_S8 :
    ∀ C : Set Behavior, Cq ⊆ C → C ⊆ Cqc → ¬ IsSemialgebraic C :=
  fun _ => QuantumBehaviors.intermediate_not_semialgebraic

theorem proposition_S9 :
    ∀ C : Set Behavior, Cq ⊆ C → C ⊆ Cqc →
    BellLocal (curve 2) ∧ ¬ IsSemianalyticAt C (curve 2) :=
  fun _ => QuantumBehaviors.intermediate_not_semianalytic

theorem remark_S10_lift :
    ∀ α : ℝ, Allowed α ↔ ∃ t : ℝ,
    (2 - α) * t = 2 ∧ Real.sin (Real.pi * t) = 0 ∧ 3 ≤ t :=
  QuantumBehaviors.allowed_iff_analytic_lift

theorem remark_S10_sine :
    ∀ α : ℝ, 1 < α → α < 2 →
    (Allowed α ↔ Real.sin (2 * Real.pi / (2 - α)) = 0) :=
  fun _ => QuantumBehaviors.allowed_iff_punctured_sine

theorem remark_S10_analytic :
    ∀ α : ℝ, α < 2 →
    AnalyticAt ℝ (fun x => Real.sin (2 * Real.pi / (2 - x))) α :=
  fun _ => QuantumBehaviors.punctured_sine_analytic

theorem corollary_S11 :
    ∀ C : Set Behavior, Cq ⊆ C → C ⊆ Cqc →
    ¬ HasFiniteSemialgebraicLift C ∧ ¬ HasFiniteSDPLift C ∧ ¬ HasFiniteComplexSDPLift C :=
  fun _ hq hqc => ⟨QuantumBehaviors.intermediate_no_finite_semialgebraic_lift hq hqc,
    QuantumBehaviors.intermediate_no_finite_sdp_lift hq hqc,
    QuantumBehaviors.intermediate_no_finite_complex_sdp_lift hq hqc⟩

theorem proposition_S13 :
    ∀ α : ℝ, 1 < α → α < 2 → ¬ BellLocal (curve α) ∧
    ∃ q : Behavior, BellLocal q ∧ ∀ i j, correlator q i j = correlator (curve α) i j :=
  fun _ => QuantumBehaviors.proposition_S13

theorem corollary_S14 :
    (∀ m : ℕ, 3 ≤ m → m / Nat.gcd m 2 ≤ Dimension.Dsr m ∧
      Dimension.Dsr m ≤ m ∧ m / Nat.gcd m 2 ≤ Dimension.D m ∧ Dimension.D m ≤ 24 * m) ∧
    (fun m => (Dimension.D m : ℝ)) =Θ[atTop] (fun m => (2 - alpha m)⁻¹) ∧
    (fun m => (Dimension.Dsr m : ℝ)) =Θ[atTop] (fun m => (2 - alpha m)⁻¹) ∧
    Tendsto (fun m => curve (alpha m)) atTop (nhds (curve 2)) ∧ BellLocal (curve 2) :=
  QuantumBehaviors.Dimension.corollary_S14

theorem dimension_each_party :
    ∀ (m dA dB : ℕ), 3 ≤ m → ∀ s : FiniteStrategy dA dB,
    s.realizes (curve (alpha m)) → m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB :=
  fun _ _ _ hm => QuantumBehaviors.Dimension.curve_finite_strategy_dimension_bound hm

theorem dimension_shared_each_party :
    ∀ m dA dB : ℕ, 3 ≤ m →
    Dimension.SharedBoundedBehavior dA dB (curve (alpha m)) →
    m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB :=
  fun _ _ _ => QuantumBehaviors.Dimension.curve_shared_dimension_bound

theorem corollary_S15 :
    ∀ (n : ℕ) (t : Model), IsSemialgebraic (Scenarios.synchronousSet n t) ↔ n ≤ 3 :=
  QuantumBehaviors.Scenarios.theorem_S15

theorem small_models_equal :
    ∀ n : ℕ, n ≤ 3 → ∀ t u : Model,
    Scenarios.synchronousSet n t = Scenarios.synchronousSet n u :=
  fun _ => QuantumBehaviors.Scenarios.synchronous_models_eq_of_le_three

theorem corollary_S16 :
    ∀ nA nB mA mB : ℕ, 4 ≤ nA → 4 ≤ nB → 2 ≤ mA → 2 ≤ mB →
    ∀ t : Model, ¬ IsSemialgebraic (Scenarios.quantumSet nA nB mA mB t) :=
  fun _ _ _ _ => QuantumBehaviors.Scenarios.larger_scenario_not_semialgebraic

theorem npa_finite_sdp :
    ∀ k : ℕ, HasFiniteComplexSDPLift (NPA.level k) :=
  QuantumBehaviors.NPA.finite_complex_sdp

theorem npa_tail :
    ∀ k : ℕ, ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2,
    curve α ∈ NPA.level k :=
  QuantumBehaviors.NPA.finite_level_tail

theorem npa_strict :
    ∀ k : ℕ, Cqc ⊂ NPA.level k :=
  QuantumBehaviors.NPA.finite_level_strict

theorem npa_complete :
    (⋂ k : ℕ, NPA.level k) = Cqc :=
  QuantumBehaviors.NPA.complete_hierarchy

theorem npa_pointwise_exclusion :
    ∀ α : ℝ, α ∈ Ioo (1 : ℝ) 2 → ¬ Allowed α →
    ∃ k, curve α ∉ NPA.level k :=
  fun _ => QuantumBehaviors.NPA.forbidden_eventually_excluded

theorem npa_no_uniform_level :
    ∀ (k : ℕ) (β : ℝ), β < 2 →
    ∃ α ∈ Ioo (max 1 β) 2, curve α ∈ NPA.level k ∧ curve α ∉ Cqc :=
  fun k _ => QuantumBehaviors.NPA.no_uniform_finite_level k

theorem almost_quantum_certificate :
    ∀ p : Behavior, p ∈ AlmostQuantum.behaviors ↔
    Nonempty (AlmostQuantum.Certificate p) :=
  QuantumBehaviors.AlmostQuantum.mem_iff_certificate

theorem almost_quantum_finite_sdp :
    HasFiniteComplexSDPLift AlmostQuantum.behaviors :=
  QuantumBehaviors.AlmostQuantum.finite_complex_sdp

theorem almost_quantum_tail :
    ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2,
    ¬ Allowed α → curve α ∈ AlmostQuantum.behaviors ∧ curve α ∉ Cqc :=
  QuantumBehaviors.AlmostQuantum.forbidden_tail

theorem almost_quantum_strict :
    Cqc ⊂ AlmostQuantum.behaviors :=
  QuantumBehaviors.AlmostQuantum.cqc_strict_subset

end PaperChecks
