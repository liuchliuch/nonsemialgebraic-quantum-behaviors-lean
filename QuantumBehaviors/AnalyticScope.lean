import QuantumBehaviors.Main
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact reciprocal membership, convergence, and the explicitly excluded singular analytic scope. -/
namespace QuantumBehaviors

open Filter Set
open scoped Topology

theorem alpha_tendsto_two : Tendsto alpha atTop (𝓝 (2 : ℝ)) := by
  simpa [alpha] using (tendsto_const_nhds (x := (2 : ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))

theorem curve_alpha_tendsto_classical : Tendsto (fun m => curve (alpha m)) atTop (𝓝 (curve 2)) :=
  (curve_continuous.tendsto 2).comp alpha_tendsto_two

theorem allowed_iff_reciprocal_nat {α : ℝ} (hα : α < 2) :
    Allowed α ↔ ∃ m : ℕ, 3 ≤ m ∧ 2 / (2 - α) = (m : ℝ) := by
  have hden : 2 - α ≠ 0 := by linarith
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨m, hm, ?_⟩
    unfold alpha
    field_simp
    ring
  · rintro ⟨m, hm, heq⟩
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨m, hm, ?_⟩
    unfold alpha
    have hmul : 2 = (m : ℝ) * (2 - α) := (div_eq_iff hden).mp heq
    field_simp
    nlinarith

/-- Remark S10: an unbounded auxiliary variable does admit the stated analytic lift. -/
theorem allowed_iff_analytic_lift (α : ℝ) :
    Allowed α ↔ ∃ t : ℝ, (2 - α) * t = 2 ∧ Real.sin (Real.pi * t) = 0 ∧ 3 ≤ t := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨m, ?_, ?_, ?_⟩
    · unfold alpha
      field_simp
      ring
    · simpa [mul_comm] using Real.sin_nat_mul_pi m
    · exact_mod_cast hm
  · rintro ⟨t, heq, hsin, ht⟩
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsin
    have hzt : (z : ℝ) = t := by nlinarith [Real.pi_pos]
    have hz3 : (3 : ℤ) ≤ z := by exact_mod_cast (hzt.symm ▸ ht)
    have hz0 : 0 ≤ z := by omega
    let m := z.toNat
    have hm : (m : ℤ) = z := Int.toNat_of_nonneg hz0
    have hmR' : (m : ℝ) = (z : ℝ) := by exact_mod_cast hm
    have hmt : (m : ℝ) = t := hmR'.trans hzt
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, hm3, ?_⟩
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    unfold alpha
    rw [← hmt] at heq
    field_simp
    nlinarith

/-- The sine function used in the scope remark is analytic at every point strictly below 2. -/
theorem punctured_sine_analytic {α : ℝ} (hα : α < 2) :
    AnalyticAt ℝ (fun x => Real.sin (2 * Real.pi / (2 - x))) α := by
  apply Real.analyticAt_sin.comp
  apply analyticAt_const.div (analyticAt_const.sub analyticAt_id)
  change (2 : ℝ) - α ≠ 0
  linarith

/-- The punctured analytic equation in Remark S10 describes precisely the allowed sequence. -/
theorem allowed_iff_punctured_sine {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    Allowed α ↔ Real.sin (2 * Real.pi / (2 - α)) = 0 := by
  have hden : 0 < 2 - α := by linarith
  have hrecip : (2 : ℝ) < 2 / (2 - α) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have heq : 2 * Real.pi / (2 - α) = Real.pi * (2 / (2 - α)) := by ring
  rw [heq]
  constructor
  · intro h
    obtain ⟨m, hm, hval⟩ := (allowed_iff_reciprocal_nat hα₂).mp h
    rw [hval]
    simpa [mul_comm] using Real.sin_nat_mul_pi m
  · intro hsin
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsin
    have hzt : (z : ℝ) = 2 / (2 - α) := by nlinarith [Real.pi_pos]
    have hz3 : (3 : ℤ) ≤ z := by
      have hz2 : (2 : ℤ) < z := by exact_mod_cast (hzt.symm ▸ hrecip)
      omega
    have hz0 : 0 ≤ z := by omega
    have hm : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
    have hmR : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hm
    apply (allowed_iff_reciprocal_nat hα₂).mpr
    exact ⟨z.toNat, by omega, hzt.symm.trans hmR.symm⟩

end QuantumBehaviors
