import QuantumBehaviors.Projection.FiniteFormula
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Finite sign determination from Tarski queries

This is the exact finite linear-algebra part of sign determination. A requested sign
pattern on any finite sample set is detected by an explicit integer linear combination
of Tarski queries of products `∏ qᵢ ^ eᵢ`, with every `eᵢ ∈ {0,1,2}`. A uniform polynomial
coefficient description of the individual Tarski queries remains a separate theorem.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open scoped BigOperators
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Twice the characteristic function of an individual sign. -/
def signSelector (target actual : SignType) : ℤ := if target = actual then 2 else 0

/-- Coefficients of the quadratic interpolation polynomial on `{-1,0,1}`. -/
def signWeight (target : SignType) (e : Fin 3) : ℤ :=
  if e = 0 then (if target = 0 then 2 else 0)
  else if e = 1 then (target : ℤ)
  else if target = 0 then -2 else 1

lemma signSelector_expansion (target actual : SignType) :
    signSelector target actual = ∑ e : Fin 3, signWeight target e * (actual : ℤ) ^ (e : ℕ) := by
  cases target <;> cases actual <;>
    norm_num [signSelector, signWeight, Fin.sum_univ_succ] <;> decide

/-- Tarski query on a finite sample set; roots are later taken without multiplicity. -/
def tarskiQuery (samples : Finset ℝ) (q : Polynomial ℝ) : ℤ :=
  ∑ x ∈ samples, (SignType.sign (q.eval x) : ℤ)

/-- Product-polynomial query associated with an exponent vector. -/
def queryPolynomial (q : ι → Polynomial ℝ) (e : ι → Fin 3) : Polynomial ℝ :=
  ∏ i, q i ^ (e i : ℕ)

lemma queryPolynomial_sign (q : ι → Polynomial ℝ) (e : ι → Fin 3) (x : ℝ) :
    (SignType.sign ((queryPolynomial q e).eval x) : ℤ) =
      ∏ i, (SignType.sign ((q i).eval x) : ℤ) ^ (e i : ℕ) := by
  simp only [queryPolynomial, eval_prod, eval_pow]
  change (SignType.castHom ((signHom : ℝ →*₀ SignType)
    (∏ i, (q i).eval x ^ (e i : ℕ))) : ℤ) = _
  simp only [map_prod, map_pow]
  rfl

/-- Explicit integer linear combination that detects a full sign vector. -/
def signDetermination (samples : Finset ℝ) (q : ι → Polynomial ℝ)
    (target : ι → SignType) : ℤ :=
  ∑ e : ι → Fin 3, (∏ i, signWeight (target i) (e i)) *
    tarskiQuery samples (queryPolynomial q e)

lemma signDetermination_eq_selectors (samples : Finset ℝ) (q : ι → Polynomial ℝ)
    (target : ι → SignType) :
    signDetermination samples q target =
      ∑ x ∈ samples, ∏ i, signSelector (target i) (SignType.sign ((q i).eval x)) := by
  classical
  simp only [signDetermination, tarskiQuery, queryPolynomial_sign, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [signSelector_expansion, Fintype.prod_sum, Finset.prod_mul_distrib]

lemma prod_signSelector_nonneg (target actual : ι → SignType) :
    0 ≤ ∏ i, signSelector (target i) (actual i) := by
  apply Finset.prod_nonneg
  intro i _
  unfold signSelector
  split_ifs <;> norm_num

lemma prod_signSelector_pos_iff (target actual : ι → SignType) :
    0 < ∏ i, signSelector (target i) (actual i) ↔ ∀ i, actual i = target i := by
  classical
  constructor
  · intro hp i
    by_contra hi
    have hz : signSelector (target i) (actual i) = 0 := by simp [signSelector, Ne.symm hi]
    have hprod : ∏ j, signSelector (target j) (actual j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hprod] at hp
    exact lt_irrefl _ hp
  · intro h
    apply Finset.prod_pos
    intro i _
    simp [signSelector, h i]

/-- All sign-pattern existence queries reduce to finitely many product-polynomial queries. -/
theorem signDetermination_pos_iff (samples : Finset ℝ) (q : ι → Polynomial ℝ)
    (target : ι → SignType) :
    0 < signDetermination samples q target ↔
      ∃ x ∈ samples, ∀ i, SignType.sign ((q i).eval x) = target i := by
  rw [signDetermination_eq_selectors]
  rw [Finset.sum_pos_iff_of_nonneg (fun x _ => prod_signSelector_nonneg target _)]
  simp only [prod_signSelector_pos_iff]

end QuantumBehaviors.Projection
