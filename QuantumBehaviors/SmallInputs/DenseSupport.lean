import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Removing degenerate objective coefficients by a quantitative perturbation.
This explicitly includes zero coefficients in the final convex-hull conclusion. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators

def momentDot (c x : Fin 6 → ℝ) : ℝ := ∑ i, c i * x i

lemma linear_functional_coordinates (f : (Fin 6 → ℝ) →L[ℝ] ℝ) (x : Fin 6 → ℝ) :
    f x = momentDot (fun i => f (Pi.single i 1)) x := by
  have he : x = ∑ i : Fin 6, x i • (Pi.single i (1 : ℝ) : Fin 6 → ℝ) := by
    funext j
    simp [Pi.single_apply]
  calc
    f x = f (∑ i : Fin 6, x i • (Pi.single i (1 : ℝ) : Fin 6 → ℝ)) := congrArg f he
    _ = momentDot (fun i => f (Pi.single i 1)) x := by
      simp only [map_sum, map_smul, smul_eq_mul, momentDot]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- It suffices to match support values for objectives with all six coefficients
nonzero. The quantitative perturbation handles every degenerate objective. -/
theorem generic_support_mem_closedConvexHull (S : Set (Fin 6 → ℝ))
    (hS : ∀ y ∈ S, ∀ i, 0 ≤ y i ∧ y i ≤ 1) (x : Fin 6 → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hsupport : ∀ c : Fin 6 → ℝ, (∀ i, c i ≠ 0) →
      ∃ y ∈ S, momentDot c x ≤ momentDot c y) : x ∈ closedConvexHull ℝ S := by
  by_contra hnot
  obtain ⟨f,u,hsep,hxu⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ) (s := S)) (isClosed_closedConvexHull (𝕜 := ℝ) (s := S)) hnot
  let c : Fin 6 → ℝ := fun i => f (Pi.single i 1)
  let ε : ℝ := (f x - u) / 12
  have hε : 0 < ε := by dsimp [ε]; linarith
  let c' : Fin 6 → ℝ := fun i => if c i = 0 then ε else c i
  have hc' : ∀ i, c' i ≠ 0 := by
    intro i
    dsimp [c']
    split_ifs with hi
    · exact hε.ne'
    · exact hi
  have hdiff : ∀ i, |c i - c' i| ≤ ε := by
    intro i
    dsimp [c']
    split_ifs with hi
    · simp [hi, abs_of_pos hε]
    · simp [hε.le]
  obtain ⟨y,hy,hxy⟩ := hsupport c' hc'
  have hfy := hsep y (subset_closedConvexHull (𝕜 := ℝ) hy)
  have herr : ∀ i, (c i - c' i) * (x i - y i) ≤ ε := by
    intro i
    have hcoord : |x i - y i| ≤ 1 := abs_le.mpr
      ⟨by have := hx i; have := hS y hy i; linarith,
        by have := hx i; have := hS y hy i; linarith⟩
    calc
      (c i - c' i) * (x i - y i) ≤ |(c i - c' i) * (x i - y i)| := le_abs_self _
      _ = |c i - c' i| * |x i - y i| := abs_mul _ _
      _ ≤ ε * 1 := mul_le_mul (hdiff i) hcoord (abs_nonneg _) hε.le
      _ = ε := mul_one _
  have hsum : (∑ i : Fin 6, (c i - c' i) * (x i - y i)) ≤ 6 * ε := by
    calc
      (∑ i : Fin 6, (c i - c' i) * (x i - y i)) ≤ ∑ _i : Fin 6, ε :=
        Finset.sum_le_sum fun i _ => herr i
      _ = 6 * ε := by simp
  have hid : f x - f y = (momentDot c' x - momentDot c' y) +
      ∑ i : Fin 6, (c i - c' i) * (x i - y i) := by
    rw [linear_functional_coordinates f x, linear_functional_coordinates f y]
    change momentDot c x - momentDot c y = _
    simp only [momentDot, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  dsimp [ε] at hsum
  linarith

end QuantumBehaviors.SmallInputs
