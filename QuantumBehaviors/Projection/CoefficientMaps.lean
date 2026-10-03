import QuantumBehaviors.Projection.RationalRepresentable
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Parameter-uniform polynomial coefficient maps

Each coefficient is represented by an actual finite rational tree, and one uniform finite
support bound is supplied. Zero and degree branches, and leading-coefficient selection,
are then finite polynomial-sign operations, including specialization degree drops.
-/

noncomputable section

namespace QuantumBehaviors.Projection

attribute [local instance] Classical.propDecidable

open Polynomial

variable {ι : Type*}

structure RationalPolynomialMap (F : (ι → ℝ) → Polynomial ℝ) : Prop where
  coeff : ∀ k : ℕ, RationallyRepresentable (fun x => (F x).coeff k)
  support_bound : ∃ N : ℕ, ∀ x k, N ≤ k → (F x).coeff k = 0

namespace RationalPolynomialMap

variable {F G : (ι → ℝ) → Polynomial ℝ}

theorem const (p : Polynomial ℝ) : RationalPolynomialMap (fun _ : ι → ℝ => p) where
  coeff := fun k => RationallyRepresentable.const (p.coeff k)
  support_bound := ⟨p.natDegree + 1, fun _ k hk => coeff_eq_zero_of_natDegree_lt (by omega)⟩

theorem ofPolynomial (p : Polynomial (MvPolynomial ι ℝ)) :
    RationalPolynomialMap (fun x => p.map (MvPolynomial.eval x)) where
  coeff := fun k => by simpa using RationallyRepresentable.polynomial (p.coeff k)
  support_bound := by
    refine ⟨p.natDegree + 1, ?_⟩
    intro x k hk
    simp only [coeff_map, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k), map_zero]

theorem add (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => F x + G x) where
  coeff := fun k => by simpa using (hF.coeff k).add (hG.coeff k)
  support_bound := by
    obtain ⟨N, hN⟩ := hF.support_bound
    obtain ⟨M, hM⟩ := hG.support_bound
    refine ⟨max N M, ?_⟩
    intro x k hk
    simp [hN x k (le_trans (le_max_left _ _) hk), hM x k (le_trans (le_max_right _ _) hk)]

theorem neg (hF : RationalPolynomialMap F) : RationalPolynomialMap (fun x => -F x) where
  coeff := fun k => by simpa using (hF.coeff k).neg
  support_bound := by
    obtain ⟨N, hN⟩ := hF.support_bound
    exact ⟨N, fun x k hk => by simp [hN x k hk]⟩

theorem sub (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem mul (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => F x * G x) where
  coeff := by
    intro k
    simpa only [coeff_mul] using RationallyRepresentable.finset_sum (Finset.antidiagonal k)
      (fun ij x => (F x).coeff ij.1 * (G x).coeff ij.2)
      (fun ij _ => (hF.coeff ij.1).mul (hG.coeff ij.2))
  support_bound := by
    obtain ⟨N, hN⟩ := hF.support_bound
    obtain ⟨M, hM⟩ := hG.support_bound
    refine ⟨N + M, ?_⟩
    intro x k hk
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have heq := Finset.mem_antidiagonal.mp hij
    by_cases hi : N ≤ ij.1
    · rw [hN x ij.1 hi, zero_mul]
    · rw [hM x ij.2 (by omega), mul_zero]

theorem derivative (hF : RationalPolynomialMap F) :
    RationalPolynomialMap (fun x => (F x).derivative) where
  coeff := fun k => by
    simpa only [coeff_derivative] using (hF.coeff (k + 1)).mul
      (RationallyRepresentable.const (k + 1 : ℝ))
  support_bound := by
    obtain ⟨N, hN⟩ := hF.support_bound
    exact ⟨N, fun x k hk => by simp [coeff_derivative, hN x (k + 1) (by omega)]⟩

theorem C {f : (ι → ℝ) → ℝ} (hf : RationallyRepresentable f) :
    RationalPolynomialMap (fun x => Polynomial.C (f x)) where
  coeff := by
    intro k
    by_cases hk : k = 0
    · simpa [hk] using hf
    · simpa [coeff_C, hk] using RationallyRepresentable.const (ι := ι) 0
  support_bound := ⟨1, fun x k hk => by simp [coeff_C, show k ≠ 0 by omega]⟩

theorem ite {C : Set (ι → ℝ)} (hC : IsSemialgebraic C)
    (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => if x ∈ C then F x else G x) where
  coeff := fun k => by
    convert RationallyRepresentable.ite hC (hF.coeff k) (hG.coeff k) using 1
    funext x
    split_ifs <;> rfl
  support_bound := by
    obtain ⟨N, hN⟩ := hF.support_bound
    obtain ⟨M, hM⟩ := hG.support_bound
    refine ⟨max N M, ?_⟩
    intro x k hk
    split_ifs <;> first
    | exact hN x k (le_trans (le_max_left _ _) hk)
    | exact hM x k (le_trans (le_max_right _ _) hk)

theorem isSemialgebraic_zero (hF : RationalPolynomialMap F) :
    IsSemialgebraic {x : ι → ℝ | F x = 0} := by
  obtain ⟨N, hN⟩ := hF.support_bound
  have hsa := isSemialgebraic_finite_forall
    (fun k : Fin N => {x : ι → ℝ | (F x).coeff k = 0})
    (fun k => (hF.coeff k).isSemialgebraic_zero)
  convert hsa using 1
  ext x
  constructor
  · intro hx k
    change F x = 0 at hx
    change (F x).coeff k = 0
    simp only [hx, coeff_zero]
  · intro hx
    apply Polynomial.ext
    intro k
    simp only [coeff_zero]
    by_cases hk : k < N
    · exact hx ⟨k, hk⟩
    · exact hN x k (Nat.le_of_not_gt hk)

theorem isSemialgebraic_natDegree_le (hF : RationalPolynomialMap F) (d : ℕ) :
    IsSemialgebraic {x : ι → ℝ | (F x).natDegree ≤ d} := by
  obtain ⟨N, hN⟩ := hF.support_bound
  have hsa := isSemialgebraic_finite_forall
    (fun k : Fin N => {x : ι → ℝ | d < (k : ℕ) → (F x).coeff k = 0}) (by
      intro k
      by_cases hk : d < (k : ℕ)
      · simpa only [hk, true_implies] using (hF.coeff k).isSemialgebraic_zero
      · simpa only [hk, false_implies, Set.setOf_true] using
          (IsSemialgebraic.univ (ι := ι)))
  convert hsa using 1
  ext x
  constructor
  · intro hx k hk
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hx hk)
  · intro hx
    apply natDegree_le_iff_degree_le.mpr
    apply (degree_le_iff_coeff_zero _ _).mpr
    intro k hk
    have hdk : d < k := by exact_mod_cast hk
    by_cases hkN : k < N
    · exact hx ⟨k, hkN⟩ hdk
    · exact hN x k (Nat.le_of_not_gt hkN)

theorem isSemialgebraic_natDegree_eq (hF : RationalPolynomialMap F) (d : ℕ) :
    IsSemialgebraic {x : ι → ℝ | (F x).natDegree = d} := by
  cases d with
  | zero => simpa only [Nat.le_zero] using hF.isSemialgebraic_natDegree_le 0
  | succ d =>
      convert (hF.isSemialgebraic_natDegree_le (d + 1)).inter
        (hF.isSemialgebraic_natDegree_le d).compl using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      omega

/-- Leading-coefficient selection is a finite guarded rational expression, including degree drops. -/
theorem leadingCoeff (hF : RationalPolynomialMap F) :
    RationallyRepresentable (fun x => (F x).leadingCoeff) := by
  obtain ⟨N, hN⟩ := hF.support_bound
  have hrep : RationallyRepresentable (fun x => ∑ k ∈ Finset.range N,
      if (F x).natDegree = k then (F x).coeff k else 0) := by
    apply RationallyRepresentable.finset_sum
    intro k hk
    convert RationallyRepresentable.ite (hF.isSemialgebraic_natDegree_eq k)
      (hF.coeff k) (RationallyRepresentable.const 0) using 1
    funext x
    by_cases hx : (F x).natDegree = k <;> simp only [Set.mem_setOf_eq, hx, ite_true, ite_false]
  convert hrep using 1
  funext x
  by_cases hz : F x = 0
  · simp [hz]
  have hlt : (F x).natDegree < N := by
    by_contra h
    exact (leadingCoeff_ne_zero.mpr hz) (hN x (F x).natDegree (Nat.le_of_not_gt h))
  rw [Finset.sum_eq_single (F x).natDegree]
  · simp only [ite_true, coeff_natDegree]
  · intro k hk hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hlt)).elim

end RationalPolynomialMap

end QuantumBehaviors.Projection
