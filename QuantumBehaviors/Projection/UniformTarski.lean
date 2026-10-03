import QuantumBehaviors.Projection.FiniteSignFunctions
import QuantumBehaviors.Projection.TarskiAlgorithm

/-!
# Uniform compilation of Tarski queries

Finite support bounds control chain length. Every chain entry is a finite guarded rational
coefficient map, and every variation count is a finite function of finitely many coefficient
signs. The unrestricted univariate query algorithm therefore specializes uniformly.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial Sturm
attribute [local instance] Classical.propDecidable

/-- Zero-padded individual entries of the signed remainder chain. -/
def chainEntry : ℕ → Polynomial ℝ → Polynomial ℝ → Polynomial ℝ
  | 0, p, _ => p
  | k + 1, p, q => if q = 0 then 0 else chainEntry k q (-(p % q))

theorem chainEntry_eq_getD (k : ℕ) (p q : Polynomial ℝ) :
    chainEntry k p q = (signedRemChain p q)[k]?.getD 0 := by
  induction k generalizing p q with
  | zero => simp [chainEntry]
  | succ k ih =>
      by_cases hq : q = 0
      · simp [chainEntry, hq]
      · simp only [chainEntry, if_neg hq, signedRemChain_of_ne_zero p hq,
          List.getElem?_cons_succ, ih]

/-- A uniform coefficient bound on the second polynomial bounds the entire chain length. -/
theorem signedRemChain_length_bound (N : ℕ) (p q : Polynomial ℝ)
    (hq : ∀ k, N ≤ k → q.coeff k = 0) : (signedRemChain p q).length ≤ N + 1 := by
  induction N generalizing p q with
  | zero =>
      have hq0 : q = 0 := by ext k; simpa using hq k (Nat.zero_le k)
      simp [hq0]
  | succ N ih =>
      by_cases hq0 : q = 0
      · simp [hq0]
      rw [signedRemChain_of_ne_zero p hq0, List.length_cons]
      have hr : ∀ k, N ≤ k → (-(p % q)).coeff k = 0 := by
        apply (degree_lt_iff_coeff_zero _ _).mp
        rw [degree_neg]
        apply (degree_mod_lt p hq0).trans_le
        apply (degree_le_iff_coeff_zero _ _).mpr
        intro k hk
        have hNk : N < k := by exact_mod_cast hk
        exact hq k (by omega)
      exact Nat.succ_le_succ (ih q (-(p % q)) hr)

namespace RationalPolynomialMap

variable {ι : Type*} {F G : (ι → ℝ) → Polynomial ℝ}

theorem chainEntry (k : ℕ) (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => Projection.chainEntry k (F x) (G x)) := by
  induction k generalizing F G with
  | zero => exact hF
  | succ k ih =>
      convert (RationalPolynomialMap.const (ι := ι) 0).ite hG.isSemialgebraic_zero
        (ih hG (hF.mod hG).neg) using 1
      funext x
      by_cases hx : G x = 0 <;> simp [Projection.chainEntry, hx]

theorem negInfCoeff (hF : RationalPolynomialMap F) :
    RationallyRepresentable (fun x => (F x).leadingCoeff * (-1 : ℝ) ^ (F x).natDegree) := by
  obtain ⟨N, hN⟩ := hF.support_bound
  have hrep : RationallyRepresentable (fun x => ∑ k ∈ Finset.range N,
      if (F x).natDegree = k then (F x).coeff k * (-1 : ℝ) ^ k else 0) := by
    apply RationallyRepresentable.finset_sum
    intro k hk
    convert RationallyRepresentable.ite (hF.isSemialgebraic_natDegree_eq k)
      ((hF.coeff k).mul (RationallyRepresentable.const ((-1 : ℝ) ^ k)))
      (RationallyRepresentable.const 0) using 1
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

theorem sturmVarPosInf (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationallyRepresentable (fun x => (Sturm.sturmVarPosInf (signedRemChain (F x) (G x)) : ℝ)) := by
  obtain ⟨N, hN⟩ := hG.support_bound
  have hrep := rationallyRepresentable_signVariations
    (fun k : Fin (N + 1) => fun x => (Projection.chainEntry k (F x) (G x)).leadingCoeff)
    (fun k => (hF.chainEntry k hG).leadingCoeff)
  convert hrep using 1
  funext x
  apply congrArg (fun n : ℕ => (n : ℝ))
  symm
  simp only [chainEntry_eq_getD]
  exact signVariations_padded_ofFn (signedRemChain (F x) (G x)) Polynomial.leadingCoeff 0
    (by simp) (N + 1) (signedRemChain_length_bound N (F x) (G x) (hN x))

theorem sturmVarNegInf (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationallyRepresentable (fun x => (Sturm.sturmVarNegInf (signedRemChain (F x) (G x)) : ℝ)) := by
  obtain ⟨N, hN⟩ := hG.support_bound
  have hrep := rationallyRepresentable_signVariations
    (fun k : Fin (N + 1) => fun x => (Projection.chainEntry k (F x) (G x)).leadingCoeff *
      (-1 : ℝ) ^ (Projection.chainEntry k (F x) (G x)).natDegree)
    (fun k => (hF.chainEntry k hG).negInfCoeff)
  convert hrep using 1
  funext x
  apply congrArg (fun n : ℕ => (n : ℝ))
  symm
  simp only [chainEntry_eq_getD]
  exact signVariations_padded_ofFn (signedRemChain (F x) (G x))
    (fun p => p.leadingCoeff * (-1 : ℝ) ^ p.natDegree) 0 (by simp) (N + 1)
    (signedRemChain_length_bound N (F x) (G x) (hN x))

/-- An unrestricted Tarski query, uniformly represented by finite guarded rational syntax. -/
theorem tarskiAlgorithm (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationallyRepresentable (fun x => (Projection.tarskiAlgorithm (F x) (G x) : ℝ)) := by
  let S := fun x => squarefreeReal (F x)
  have hS : RationalPolynomialMap S := hF.div (hF.gcd hF.derivative)
  let A := fun x => activeRootPolynomial (S x) (G x)
  have hA : RationalPolynomialMap A := hS.div (hS.gcd hG)
  have hB : RationalPolynomialMap (fun x => (A x).derivative * G x) := hA.derivative.mul hG
  have hdiff := (hA.sturmVarNegInf hB).sub (hA.sturmVarPosInf hB)
  convert RationallyRepresentable.ite hF.isSemialgebraic_zero
    (RationallyRepresentable.const (ι := ι) 0) hdiff using 1
  funext x
  by_cases hx : F x = 0 <;> simp [Projection.tarskiAlgorithm, hx, S, A]

end RationalPolynomialMap

end QuantumBehaviors.Projection
