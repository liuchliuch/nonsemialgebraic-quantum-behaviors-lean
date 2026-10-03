import QuantumBehaviors.CyclicReduction
import QuantumBehaviors.SpectralClassification
import Mathlib.Tactic.LinearCombination

/-! Synchrony and the zero variance witness in the actual commuting-operator model. -/

namespace QuantumBehaviors

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem selfadjoint_inner_left (P : H →L[ℂ] H) (hP : IsSelfAdjoint P) (x y : H) :
    inner ℂ (P x) y = inner ℂ x (P y) := by
  exact hP.isSymmetric x y

private theorem projection_inner_self (P : H →L[ℂ] H) (hP : IsStarProjection P) (ψ : H) :
    inner ℂ (P ψ) (P ψ) = inner ℂ ψ (P ψ) := by
  rw [selfadjoint_inner_left P hP.isSelfAdjoint]
  have h := congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
  simpa only [ContinuousLinearMap.mul_apply] using congrArg (inner ℂ ψ) h

theorem commuting_synchrony_vector (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) (i : Input) :
    s.alice i s.state = s.bob i s.state := by
  let A := s.alice i
  let B := s.bob i
  let ψ := s.state
  have hA := s.alice_projection i
  have hB := s.bob_projection i
  have hAB : A (B ψ) = B (A ψ) :=
    congrArg (fun T : H →L[ℂ] H => T ψ) (s.cross_commute i i).eq
  have h10 : inner ℂ ψ (A ψ) - inner ℂ ψ (A (B ψ)) = 0 := by
    have hp := hreal i i true false
    rw [(hsync i).1] at hp
    simpa [effect, ψ, A, B, ContinuousLinearMap.mul_apply, map_sub, inner_sub_right] using hp.symm
  have h01 : inner ℂ ψ (B ψ) - inner ℂ ψ (A (B ψ)) = 0 := by
    have hp := hreal i i false true
    rw [(hsync i).2] at hp
    simpa [effect, ψ, A, B, ContinuousLinearMap.mul_apply, inner_sub_right] using hp.symm
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    projection_inner_self A hA ψ, projection_inner_self B hB ψ,
    selfadjoint_inner_left A hA.isSelfAdjoint,
    selfadjoint_inner_left B hB.isSelfAdjoint, ← hAB]
  linear_combination h10 + h01

theorem commuting_diagonal_moment (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) (i : Input) :
    inner ℂ s.state (s.alice i s.state) = (p (i, i, true, true) : ℂ) := by
  have hv := commuting_synchrony_vector s hreal hsync i
  have hp := hreal i i true true
  simp only [effect_true, ContinuousLinearMap.mul_apply] at hp
  rw [← hv] at hp
  have hid := congrArg (fun T : H →L[ℂ] H => T s.state)
    (s.alice_projection i).isIdempotentElem.eq
  simp only [ContinuousLinearMap.mul_apply] at hid
  rw [hid] at hp
  exact hp.symm

theorem commuting_joint_moment (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) (i j : Input) :
    inner ℂ (s.alice i s.state) (s.alice j s.state) = (p (i, j, true, true) : ℂ) := by
  rw [selfadjoint_inner_left (s.alice i) (s.alice_projection i).isSelfAdjoint,
    commuting_synchrony_vector s hreal hsync j]
  exact (hreal i j true true).symm

theorem commuting_witness_inner (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) (α : ℝ) :
    inner ℂ ((∑ i, s.alice i) s.state - (α : ℂ) • s.state)
      ((∑ i, s.alice i) s.state - (α : ℂ) • s.state) = (witness p α : ℂ) := by
  have hψ : inner ℂ s.state s.state = 1 := by
    rw [inner_self_eq_norm_sq_to_K, s.state_norm]
    norm_num
  have hfirst : inner ℂ s.state ((∑ i, s.alice i) s.state) =
      ∑ i, (p (i, i, true, true) : ℂ) := by
    simp only [ContinuousLinearMap.sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact commuting_diagonal_moment s hreal hsync i
  have hleft : inner ℂ ((∑ i, s.alice i) s.state) s.state =
      ∑ i, (p (i, i, true, true) : ℂ) := by
    simp only [ContinuousLinearMap.sum_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [selfadjoint_inner_left (s.alice i) (s.alice_projection i).isSelfAdjoint]
    exact commuting_diagonal_moment s hreal hsync i
  have hsecond : inner ℂ ((∑ i, s.alice i) s.state) ((∑ i, s.alice i) s.state) =
      ∑ i, ∑ j, (p (i, j, true, true) : ℂ) := by
    simp only [ContinuousLinearMap.sum_apply]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact commuting_joint_moment s hreal hsync i j
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_right, inner_smul_left, inner_smul_left, inner_smul_right,
    hsecond, hleft, hfirst, hψ]
  simp only [Complex.star_def, Complex.conj_ofReal, witness, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

theorem commuting_witness_zero_scalar (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) {α : ℝ} (hF : witness p α = 0) :
    (∑ i, s.alice i) s.state = (α : ℂ) • s.state := by
  have hinner := commuting_witness_inner s hreal hsync α
  rw [hF, Complex.ofReal_zero] at hinner
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hinner)

/-- Lemma S6: actual Hilbert-space projections with scalar sum, with no faithfulness assumption. -/
theorem synchronous_zero_witness_projections (s : CommutingStrategy H) {p : Behavior}
    (hreal : s.realizes p) (hsync : Synchronous p) {α : ℝ} (hF : witness p α = 0) :
    ∃ (K : Submodule ℂ H) (_ : CompleteSpace K) (_ : Nontrivial K)
      (P : Input → K →L[ℂ] K),
      (∀ i, IsStarProjection (P i)) ∧
      (∑ i, P i) = algebraMap ℝ (K →L[ℂ] K) α :=
  synchronized_scalar_restriction s α (commuting_synchrony_vector s hreal hsync)
    (commuting_witness_zero_scalar s hreal hsync hF)

/-- Necessity in the largest model, hence the hard inclusion of Theorem S7. -/
theorem curve_commuting_only_allowed {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2)
    (hmem : curve α ∈ Cqc) : Allowed α := by
  obtain ⟨H, hNorm, hInner, hComplete, s, hreal⟩ := hmem
  letI : NormedAddCommGroup H := hNorm
  letI : InnerProductSpace ℂ H := hInner
  letI : CompleteSpace H := hComplete
  obtain ⟨K, hKC, hKN, P, hP, hsum⟩ := synchronous_zero_witness_projections
    s hreal (curve_synchronous α) (curve_witness α)
  letI : CompleteSpace K := hKC
  letI : Nontrivial K := hKN
  exact four_indexed_projections_allowed P hP hsum hα₁ hα₂

end QuantumBehaviors
