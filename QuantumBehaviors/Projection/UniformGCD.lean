import QuantumBehaviors.Projection.UniformDivision

/-! # Parameter-uniform Euclidean gcd by a fixed degree budget -/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial
attribute [local instance] Classical.propDecidable

def boundedGCD : ℕ → Polynomial ℝ → Polynomial ℝ → Polynomial ℝ
  | 0, _, q => q
  | n + 1, p, q => if p = 0 then q else boundedGCD n (q % p) p

theorem boundedGCD_correct (n : ℕ) (p q : Polynomial ℝ)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) : boundedGCD n p q = EuclideanDomain.gcd p q := by
  induction n generalizing p q with
  | zero =>
      have hz : p = 0 := by ext k; simpa using hp k (Nat.zero_le k)
      simp [boundedGCD, hz, EuclideanDomain.gcd_zero_left]
  | succ n ih =>
      rw [boundedGCD]
      split_ifs with hz
      · simp [hz, EuclideanDomain.gcd_zero_left]
      · rw [ih]
        · exact (EuclideanDomain.gcd_val p q).symm
        · apply (degree_lt_iff_coeff_zero _ _).mp
          apply (degree_mod_lt q hz).trans_le
          apply (degree_le_iff_coeff_zero _ _).mpr
          intro k hk
          have hnk : n < k := by exact_mod_cast hk
          exact hp k (by omega)

namespace RationalPolynomialMap

variable {ι : Type*} {F G : (ι → ℝ) → Polynomial ℝ}

theorem boundedGCD (n : ℕ) (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => Projection.boundedGCD n (F x) (G x)) := by
  induction n generalizing F G with
  | zero => exact hG
  | succ n ih =>
      convert hG.ite hF.isSemialgebraic_zero (ih (hG.mod hF) hF) using 1
      funext x
      by_cases hx : F x = 0 <;> simp [Projection.boundedGCD, Set.mem_setOf_eq, hx]

theorem gcd (hF : RationalPolynomialMap F) (hG : RationalPolynomialMap G) :
    RationalPolynomialMap (fun x => EuclideanDomain.gcd (F x) (G x)) := by
  obtain ⟨N, hN⟩ := hF.support_bound
  convert hF.boundedGCD N hG using 1
  funext x
  exact (boundedGCD_correct N (F x) (G x) (hN x)).symm

end RationalPolynomialMap

end QuantumBehaviors.Projection
