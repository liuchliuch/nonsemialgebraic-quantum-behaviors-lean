import QuantumBehaviors.Parameters
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Nat.GCD.Basic

/-! Trace integrality and exact denominator divisibility for finite scalar projection sums. -/
namespace QuantumBehaviors

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem idempotent_trace_natural (P : Matrix ι ι ℂ) (hP : P * P = P) :
    ∃ r : ℕ, P.trace = (r : ℂ) := by
  have hlin : IsIdempotentElem P.toLin' := by
    change P.toLin' * P.toLin' = P.toLin'
    simpa only [← Matrix.toLin'_mul, Module.End.mul_eq_comp] using congrArg Matrix.toLin' hP
  refine ⟨Module.finrank ℂ (LinearMap.range P.toLin'), ?_⟩
  simpa only [Matrix.trace_toLin'_eq] using (LinearMap.IsIdempotentElem.isProj_range P.toLin' hlin).trace

theorem scalar_sum_trace_integral (P : Input → Matrix ι ι ℂ)
    (hP : ∀ i, P i * P i = P i) {α : ℝ}
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : Matrix ι ι ℂ)) :
    ∃ r : ℕ, α * (Fintype.card ι : ℝ) = r := by
  choose r hr using fun i => idempotent_trace_natural (P i) (hP i)
  refine ⟨∑ i, r i, ?_⟩
  have ht := congrArg Matrix.trace hsum
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one, hr, smul_eq_mul] at ht
  have hreal := congrArg Complex.re ht.symm
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero, map_sum, Nat.cast_sum] using hreal

theorem denominator_divides_of_integral {m d r : ℕ} (hm : 3 ≤ m)
    (h : alpha m * (d : ℝ) = r) : m ∣ 2 * d := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hα := (alpha_mem_Ioo hm).2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hleR : (r : ℝ) ≤ 2 * d := by nlinarith
  have hle : r ≤ 2 * d := by exact_mod_cast hleR
  have hmul : (2 * (m : ℝ) - 2) * d = r * m := by
    dsimp [alpha] at h
    field_simp at h
    nlinarith
  refine ⟨2 * d - r, ?_⟩
  have heq : (2 * d : ℝ) = (m : ℝ) * ((2 * d - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]
    push_cast
    nlinarith
  exact_mod_cast heq

theorem reduced_denominator_dvd {m d : ℕ} (hm : 0 < m) (h : m ∣ 2 * d) :
    m / Nat.gcd m 2 ∣ d := by
  have hg : 0 < Nat.gcd m 2 := Nat.gcd_pos_of_pos_left 2 hm
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  have hdiv : m / Nat.gcd m 2 ∣ (2 / Nat.gcd m 2) * d := by
    apply (Nat.mul_dvd_mul_iff_left hg).mp
    simpa only [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left m 2),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right m 2)] using h
  exact hcop.dvd_of_dvd_mul_left hdiv

/-- The exact rank-integrality lower bound whenever a genuine finite scalar-sum reduction is given. -/
theorem scalar_projection_dimension_bound (P : Input → Matrix ι ι ℂ) [Nonempty ι]
    (hP : ∀ i, P i * P i = P i) {m : ℕ} (hm : 3 ≤ m)
    (hsum : (∑ i, P i) = (alpha m : ℂ) • (1 : Matrix ι ι ℂ)) :
    m / Nat.gcd m 2 ≤ Fintype.card ι := by
  obtain ⟨r, hr⟩ := scalar_sum_trace_integral P hP hsum
  have hdiv := denominator_divides_of_integral hm hr
  exact Nat.le_of_dvd Fintype.card_pos (reduced_denominator_dvd (by omega) hdiv)

end QuantumBehaviors
