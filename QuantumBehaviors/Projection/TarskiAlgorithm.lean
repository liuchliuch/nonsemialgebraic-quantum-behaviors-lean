import QuantumBehaviors.Projection.RootReduction

/-!
# Unrestricted univariate Tarski-query algorithm

The algorithm uses only gcd, derivative, division, a terminating signed-remainder chain,
and signs of leading coefficients. Repeated roots, common roots, zero polynomials, and
constant polynomials are included. Uniform specialization of these coefficient operations
into finite polynomial-sign branch trees is proved separately in `UniformTarski.lean`;
this file supplies the univariate correctness theorem used there.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial Sturm

lemma squarefreeReal_roots {p : Polynomial ℝ} (hp : p ≠ 0) :
    (squarefreeReal p).roots.toFinset = p.roots.toFinset := by
  ext x
  simp only [Multiset.mem_toFinset, Polynomial.mem_roots (squarefreeReal_ne_zero hp),
    Polynomial.mem_roots hp, IsRoot]
  exact squarefreeReal_eval_zero_iff hp x

lemma activeRootPolynomial_query {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p p.derivative) :
    tarskiQuery p.roots.toFinset q = tarskiQuery (activeRootPolynomial p q).roots.toFinset q := by
  classical
  have hsub : (activeRootPolynomial p q).roots.toFinset ⊆ p.roots.toFinset := by
    intro x hx
    have hz := (Polynomial.mem_roots (activeRootPolynomial_ne_zero (q := q) hp)).mp
      (Multiset.mem_toFinset.mp hx)
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
      (((activeRootPolynomial_eval_zero_iff hp h x).mp hz).1))
  unfold tarskiQuery
  symm
  apply Finset.sum_subset hsub
  intro x hx hnot
  have hpz : p.eval x = 0 := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hx)
  by_cases hq : q.eval x = 0
  · simp [hq]
  · exact (hnot (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (activeRootPolynomial_ne_zero (q := q) hp)).mpr
        ((activeRootPolynomial_eval_zero_iff hp h x).mpr ⟨hpz, hq⟩)))).elim

/-- A coefficient-arithmetic algorithm for the integer Tarski query. -/
def tarskiAlgorithm (p q : Polynomial ℝ) : ℤ :=
  if p = 0 then 0 else
    let a := activeRootPolynomial (squarefreeReal p) q
    let chain := signedRemChain a (a.derivative * q)
    (sturmVarNegInf chain : ℤ) - sturmVarPosInf chain

/-- Full correctness for every pair of real polynomials, without simplicity/coprimality premises. -/
theorem tarskiAlgorithm_correct (p q : Polynomial ℝ) :
    tarskiAlgorithm p q = tarskiQuery p.roots.toFinset q := by
  classical
  by_cases hp : p = 0
  · simp [tarskiAlgorithm, hp, tarskiQuery]
  let s := squarefreeReal p
  have hs : s ≠ 0 := squarefreeReal_ne_zero hp
  have hsd : NoCommonRealRoot s s.derivative := squarefreeReal_simple hp
  let a := activeRootPolynomial s q
  have ha : a ≠ 0 := activeRootPolynomial_ne_zero hs
  have had : NoCommonRealRoot a a.derivative := activeRootPolynomial_simple hs hsd
  have haq : NoCommonRealRoot a q := activeRootPolynomial_weight_nonzero hs hsd
  change (if p = 0 then 0 else
    (sturmVarNegInf (signedRemChain a (a.derivative * q)) : ℤ) -
      sturmVarPosInf (signedRemChain a (a.derivative * q))) = _
  rw [if_neg hp, ← sturmTarski_simple ha had haq, ← activeRootPolynomial_query hs hsd]
  change tarskiQuery (squarefreeReal p).roots.toFinset q = _
  rw [squarefreeReal_roots hp]

/-- Exact sign-pattern detection by finitely many calls to the proved coefficient algorithm. -/
theorem signDetermination_algorithm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Polynomial ℝ) (q : ι → Polynomial ℝ) (target : ι → SignType) :
    (0 : ℤ) < ∑ e : ι → Fin 3,
        (∏ i, signWeight (target i) (e i)) * tarskiAlgorithm p (queryPolynomial q e) ↔
      ∃ x ∈ p.roots.toFinset, ∀ i, SignType.sign ((q i).eval x) = target i := by
  simp only [tarskiAlgorithm_correct]
  exact signDetermination_pos_iff _ _ _

end QuantumBehaviors.Projection
