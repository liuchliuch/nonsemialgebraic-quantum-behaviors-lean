import QuantumBehaviors.Projection.CoefficientMaps
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Uniform finite polynomial division

A fixed coefficient budget gives a finite long-division expression. Only the divisor's
specialized degree is branched on. Each branch is already a finite polynomial-sign
formula, so division of coefficient-rational polynomial families remains coefficient-rational.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial
attribute [local instance] Classical.propDecidable

lemma polynomial_div_sub_mul (p q l : Polynomial ℝ) (hq : q ≠ 0) :
    (p - q * l) / q = p / q - l := by
  have hmod : (p - q * l) % q = p % q := by
    rw [Polynomial.sub_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right q l), sub_zero]
  apply mul_left_cancel₀ hq
  have h1 := EuclideanDomain.div_add_mod p q
  have h2 := EuclideanDomain.div_add_mod (p - q * l) q
  rw [hmod] at h2
  linear_combination h2 - h1

/-- Long division with a fixed coefficient budget, using a fixed divisor-degree branch. -/
def boundedQuotient : ℕ → ℕ → Polynomial ℝ → Polynomial ℝ → Polynomial ℝ
  | 0, _, _, _ => 0
  | n + 1, m, p, q =>
      if m ≤ n then
        let l := monomial (n - m) (p.coeff n / q.coeff m)
        l + boundedQuotient n m (p - q * l) q
      else 0

lemma coefficient_elimination_bound (n m : ℕ) (p q : Polynomial ℝ)
    (hp : ∀ k, n + 1 ≤ k → p.coeff k = 0)
    (hq : q ≠ 0) (hqm : q.natDegree = m) (hm : m ≤ n) :
    ∀ k, n ≤ k →
      (p - q * monomial (n - m) (p.coeff n / q.coeff m)).coeff k = 0 := by
  have hqm0 : q.coeff m ≠ 0 := by
    rw [← hqm]
    exact leadingCoeff_ne_zero.mpr hq
  have hprod : (q * monomial (n - m) (p.coeff n / q.coeff m)).natDegree ≤ n := by
    apply (natDegree_mul_le).trans
    rw [hqm]
    have hm' : (monomial (n - m) (p.coeff n / q.coeff m) : Polynomial ℝ).natDegree ≤ n - m :=
      natDegree_monomial_le _
    omega
  intro k hk
  rw [coeff_sub]
  rcases hk.eq_or_lt with rfl | hnk
  · have heq : m + (n - m) = n := Nat.add_sub_of_le hm
    have hc := coeff_mul_monomial q (n - m) m (p.coeff n / q.coeff m)
    rw [heq] at hc
    rw [hc, mul_div_cancel₀ _ hqm0, sub_self]
  · rw [hp k (by omega), coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprod hnk), sub_self]

/-- The fixed-budget expression equals actual polynomial division. -/
theorem boundedQuotient_correct (n m : ℕ) (p q : Polynomial ℝ)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) (hq : q ≠ 0) (hqm : q.natDegree = m) :
    boundedQuotient n m p q = p / q := by
  induction n generalizing p with
  | zero =>
      have hp0 : p = 0 := by ext k; simpa using hp k (Nat.zero_le k)
      simp [boundedQuotient, hp0]
  | succ n ih =>
      rw [boundedQuotient]
      split_ifs with hm
      · dsimp only
        rw [ih _ (coefficient_elimination_bound n m p q hp hq hqm hm),
          polynomial_div_sub_mul _ _ _ hq]
        abel
      · symm
        apply (Polynomial.div_eq_zero_iff hq).mpr
        have hd : p.degree < (n + 1 : ℕ) := (degree_lt_iff_coeff_zero _ _).mpr hp
        rw [degree_eq_natDegree hq, hqm]
        exact hd.trans_le (by exact_mod_cast (show n + 1 ≤ m by omega))

namespace RationalPolynomialMap

variable {ι α : Type*} {F G : (ι → ℝ) → Polynomial ℝ}

theorem monomial {f : (ι → ℝ) → ℝ} (hf : RationallyRepresentable f) (k : ℕ) :
    RationalPolynomialMap (fun x => Polynomial.monomial k (f x)) := by
  convert (RationalPolynomialMap.C hf).mul (RationalPolynomialMap.const (X ^ k)) using 1
  funext x
  exact C_mul_X_pow_eq_monomial.symm

theorem finset_sum (s : Finset α) (F : α → (ι → ℝ) → Polynomial ℝ)
    (hF : ∀ i ∈ s, RationalPolynomialMap (F i)) :
    RationalPolynomialMap (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RationalPolynomialMap.const (ι := ι) 0
  | @insert a s has ih =>
      simpa only [Finset.sum_insert has] using (hF a (by simp)).add
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem boundedQuotient (n m : ℕ) (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => Projection.boundedQuotient n m (F x) (G x)) := by
  induction n generalizing F with
  | zero => exact RationalPolynomialMap.const 0
  | succ n ih =>
      by_cases hm : m ≤ n
      · let L := fun x => Polynomial.monomial (n - m) ((F x).coeff n / (G x).coeff m)
        have hL : RationalPolynomialMap L := RationalPolynomialMap.monomial ((hF.coeff n).div (hG.coeff m)) (n - m)
        simpa only [Projection.boundedQuotient, if_pos hm] using
          hL.add (ih (hF.sub (hG.mul hL)))
      · simpa only [Projection.boundedQuotient, if_neg hm] using
          (RationalPolynomialMap.const (ι := ι) 0)

/-- Division handles zero divisors and every possible specialized degree in finitely many branches. -/
theorem div (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => F x / G x) := by
  classical
  obtain ⟨N, hN⟩ := hF.support_bound
  obtain ⟨M, hM⟩ := hG.support_bound
  let C := fun m => {x : ι → ℝ | G x ≠ 0 ∧ (G x).natDegree = m}
  have hC : ∀ m, IsSemialgebraic (C m) := by
    intro m
    exact hG.isSemialgebraic_zero.compl.inter (hG.isSemialgebraic_natDegree_eq m)
  have hrep : RationalPolynomialMap (fun x => ∑ m ∈ Finset.range M,
      if x ∈ C m then Projection.boundedQuotient N m (F x) (G x) else 0) := by
    apply finset_sum
    intro m hm
    convert (hF.boundedQuotient N m hG).ite (hC m) (RationalPolynomialMap.const 0) using 1
    funext x
    by_cases hx : x ∈ C m <;> simp only [hx, ite_true, ite_false]
  convert hrep using 1
  funext x
  by_cases hg : G x = 0
  · simp [C, hg]
  have hdeg : (G x).natDegree < M := by
    by_contra h
    exact (leadingCoeff_ne_zero.mpr hg) (hM x (G x).natDegree (Nat.le_of_not_gt h))
  rw [Finset.sum_eq_single (G x).natDegree]
  · have hx : x ∈ C (G x).natDegree := ⟨hg, rfl⟩
    rw [if_pos hx]
    exact (boundedQuotient_correct N _ _ _ (hN x) hg rfl).symm
  · intro m hm hne
    have hx : x ∉ C m := fun h => hne h.2.symm
    rw [if_neg hx]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hdeg)).elim

/-- Remainder follows from the proved division formula by ring operations. -/
theorem mod (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => F x % G x) := by
  simpa only [EuclideanDomain.mod_eq_sub_mul_div] using hF.sub (hG.mul (hF.div hG))

end RationalPolynomialMap

end QuantumBehaviors.Projection
