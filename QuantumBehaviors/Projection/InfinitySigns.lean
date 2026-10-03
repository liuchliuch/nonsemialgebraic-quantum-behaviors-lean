import QuantumBehaviors.Projection.SignSampling
import Mathlib.Analysis.Polynomial.Basic

/-!
# Polynomial signs at infinity

The two unbounded samples in `polynomial_sign_sampling` are read from the leading
coefficient and degree parity. These are the exact signs, including zero polynomials.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Polynomial

/-- The eventual sign of a polynomial on the positive unbounded interval. -/
theorem polynomial_eventually_sign_atTop (p : Polynomial ℝ) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg)
  rcases hlc.lt_or_gt with hneg | hpos
  · filter_upwards [(p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg.le).eventually
      (eventually_lt_atBot 0)] with x hx
    rw [sign_neg hx, sign_neg hneg]
  · filter_upwards [(p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hpos.le).eventually
      (eventually_gt_atTop 0)] with x hx
    rw [sign_pos hx, sign_pos hpos]

/-- The eventual sign on the negative unbounded interval, with its degree parity. -/
theorem polynomial_eventually_sign_atBot (p : Polynomial ℝ) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) =
      SignType.sign (p.leadingCoeff * (-1 : ℝ) ^ p.natDegree) := by
  have h := (polynomial_eventually_sign_atTop (p.comp (-X))).filter_mono
    (show Filter.map (fun x : ℝ => -x) atBot ≤ atTop from tendsto_neg_atBot_atTop)
  have hlc : (p.comp (-X)).leadingCoeff = p.leadingCoeff * (-1 : ℝ) ^ p.natDegree := by
    rw [leadingCoeff_comp (by simp)]
    simp
  simpa only [Filter.eventually_map, eval_comp, eval_neg, eval_X, neg_neg, hlc] using h

/-- Nonlinear existence reduces exactly to two coefficient-sign vectors and root-sign queries. -/
theorem polynomial_formula_sampling {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) (φ : SignFormula ι) :
    (∃ t : ℝ, φ.eval (fun i => SignType.sign ((p i).eval t)) = true) ↔
    φ.eval (fun i => SignType.sign ((p i).leadingCoeff * (-1 : ℝ) ^ (p i).natDegree)) = true ∨
    φ.eval (fun i => SignType.sign (p i).leadingCoeff) = true ∨
    ∃ t : ℝ, ((rootProduct p).eval t = 0 ∨ (rootProduct p).derivative.eval t = 0) ∧
      φ.eval (fun i => SignType.sign ((p i).eval t)) = true := by
  have hbot : ∀ᶠ t in atBot, ∀ i, SignType.sign ((p i).eval t) =
      SignType.sign ((p i).leadingCoeff * (-1 : ℝ) ^ (p i).natDegree) :=
    Filter.eventually_all.mpr fun i => polynomial_eventually_sign_atBot (p i)
  have htop : ∀ᶠ t in atTop, ∀ i, SignType.sign ((p i).eval t) =
      SignType.sign (p i).leadingCoeff :=
    Filter.eventually_all.mpr fun i => polynomial_eventually_sign_atTop (p i)
  constructor
  · rintro ⟨t, ht⟩
    rcases polynomial_sign_sampling p t with h | h | ⟨x, hx, heq⟩
    · obtain ⟨x, hx, hx'⟩ := (h.and hbot).exists
      left
      have heq : (fun i => SignType.sign ((p i).leadingCoeff * (-1 : ℝ) ^ (p i).natDegree)) =
          (fun i => SignType.sign ((p i).eval t)) := funext fun i => (hx' i).symm.trans (hx i)
      rw [heq]
      exact ht
    · obtain ⟨x, hx, hx'⟩ := (h.and htop).exists
      right; left
      have heq : (fun i => SignType.sign (p i).leadingCoeff) =
          (fun i => SignType.sign ((p i).eval t)) := funext fun i => (hx' i).symm.trans (hx i)
      rw [heq]
      exact ht
    · right; right
      refine ⟨x, hx, ?_⟩
      rw [funext heq]
      exact ht
  · rintro (h | h | ⟨x, _, hx⟩)
    · obtain ⟨x, hx⟩ := hbot.exists
      refine ⟨x, ?_⟩
      rw [funext hx]
      exact h
    · obtain ⟨x, hx⟩ := htop.exists
      refine ⟨x, ?_⟩
      rw [funext hx]
      exact h
    · exact ⟨x, hx⟩

end QuantumBehaviors.Projection
