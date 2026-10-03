import QuantumBehaviors.DimensionArithmetic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact original-dimension trace bounds on the range of a nonzero coefficient matrix. -/
namespace QuantumBehaviors.Dimension

open scoped BigOperators

lemma end_scalar_trace_integral {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (P : Input → V →ₗ[ℂ] V) (hP : ∀ i, IsIdempotentElem (P i)) {α : ℝ}
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : V →ₗ[ℂ] V)) :
    ∃ r : ℕ, α * (Module.finrank ℂ V : ℝ) = r := by
  let r := fun i => Module.finrank ℂ (LinearMap.range (P i))
  have hr : ∀ i, LinearMap.trace ℂ V (P i) = (r i : ℂ) := fun i =>
    (LinearMap.IsIdempotentElem.isProj_range (P i) (hP i)).trace
  refine ⟨∑ i, r i, ?_⟩
  have ht := congrArg (LinearMap.trace ℂ V) hsum
  simp only [map_sum, map_smul, LinearMap.trace_one, hr, smul_eq_mul] at ht
  have hreal := congrArg Complex.re ht.symm
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero, map_sum, Nat.cast_sum] using hreal

/-- This is the algebraic support restriction needed in the S14 lower bound. -/
theorem coefficient_range_integrality {dA dB : ℕ}
    (Ψ : Matrix (Fin dA) (Fin dB) ℂ) (hΨ : Ψ ≠ 0)
    (E : Input → Matrix (Fin dA) (Fin dA) ℂ) (G : Input → Matrix (Fin dB) (Fin dB) ℂ)
    (hintertwine : ∀ i, E i * Ψ = Ψ * G i)
    (hidem : ∀ i, (E i * E i) * Ψ = E i * Ψ)
    {α : ℝ} (hscalar : (∑ i, E i) * Ψ = (α : ℂ) • Ψ) :
    ∃ r k : ℕ, 0 < r ∧ r ≤ dA ∧ α * (r : ℝ) = k := by
  let K : Submodule ℂ (Fin dA → ℂ) := LinearMap.range Ψ.toLin'
  have hnonzero : Ψ.toLin' ≠ 0 := by
    intro h
    apply hΨ
    apply Matrix.toLin'.injective
    simpa only [map_zero] using h
  have hK : K ≠ ⊥ := by
    change LinearMap.range Ψ.toLin' ≠ ⊥
    intro h
    exact hnonzero (LinearMap.range_eq_bot.mp h)
  letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
  have hInv : ∀ i v, v ∈ K → (E i).toLin' v ∈ K := by
    intro i v hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨(G i).toLin' w, ?_⟩
    have h := congrArg (fun M => Matrix.toLin' M w) (hintertwine i)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply] using h.symm
  let P : Input → K →ₗ[ℂ] K := fun i => (E i).toLin'.restrict (hInv i)
  have hP : ∀ i, IsIdempotentElem (P i) := by
    intro i
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨w, hw⟩ := x.property
    change (E i).toLin' ((E i).toLin' (x : Fin dA → ℂ)) = (E i).toLin' (x : Fin dA → ℂ)
    rw [← hw]
    have h := congrArg (fun M => Matrix.toLin' M w) (hidem i)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_apply] using h
  have hsumP : (∑ i, P i) = (α : ℂ) • (1 : K →ₗ[ℂ] K) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨w, hw⟩ := x.property
    have h := congrArg (fun M => Matrix.toLin' M w) hscalar
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply] at h
    simpa [P, LinearMap.sum_apply, ← hw] using h
  obtain ⟨k, hk⟩ := end_scalar_trace_integral P hP hsumP
  refine ⟨Module.finrank ℂ K, k, ?_, ?_, hk⟩
  · exact Module.finrank_pos
  · simpa using K.finrank_le

/-- A denominator-sized lower bound without enlarging either local coefficient space. -/
theorem coefficient_range_dimension_bound {dA dB m : ℕ} (hm : 3 ≤ m)
    (Ψ : Matrix (Fin dA) (Fin dB) ℂ) (hΨ : Ψ ≠ 0)
    (E : Input → Matrix (Fin dA) (Fin dA) ℂ) (G : Input → Matrix (Fin dB) (Fin dB) ℂ)
    (hintertwine : ∀ i, E i * Ψ = Ψ * G i)
    (hidem : ∀ i, (E i * E i) * Ψ = E i * Ψ)
    (hscalar : (∑ i, E i) * Ψ = (alpha m : ℂ) • Ψ) :
    m / Nat.gcd m 2 ≤ dA := by
  obtain ⟨r, k, hr, hrA, htrace⟩ := coefficient_range_integrality Ψ hΨ E G hintertwine hidem hscalar
  exact (Nat.le_of_dvd hr (reduced_denominator_dvd (by omega)
    (denominator_divides_of_integral hm htrace))).trans hrA

end QuantumBehaviors.Dimension
