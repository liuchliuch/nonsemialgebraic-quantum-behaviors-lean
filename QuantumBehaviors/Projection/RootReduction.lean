import QuantumBehaviors.Projection.SturmTarski

/-!
# Removing multiplicities and zero-weight roots

All reductions are formed by polynomial EuclideanDomain.gcd and exact quotient operations on the input
coefficients. No real-root choices enter the constructed polynomials.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial

lemma polynomial_gcd_ne_zero_left {p q : Polynomial ℝ} (hp : p ≠ 0) : EuclideanDomain.gcd p q ≠ 0 := by
  intro hg
  have hdiv := EuclideanDomain.gcd_dvd_left p q
  rw [hg, zero_dvd_iff] at hdiv
  exact hp hdiv

lemma polynomial_div_factor {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ∣ p) :
    q * (p / q) = p := by
  apply EuclideanDomain.mul_div_cancel' ?_ hq
  intro hq0
  rw [hq0, zero_dvd_iff] at hq
  exact hp hq

lemma polynomial_exact_quotient_ne_zero {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ∣ p) :
    p / q ≠ 0 := by
  intro h
  have heq := polynomial_div_factor hp hq
  rw [h, mul_zero] at heq
  exact hp heq.symm

lemma rootMultiplicity_gcd_eq_min {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (x : ℝ) :
    (EuclideanDomain.gcd p q).rootMultiplicity x = min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  have hg := polynomial_gcd_ne_zero_left (q := q) hp
  apply le_antisymm
  · exact le_min (rootMultiplicity_le_rootMultiplicity_of_dvd hp (EuclideanDomain.gcd_dvd_left p q) x)
      (rootMultiplicity_le_rootMultiplicity_of_dvd hq (EuclideanDomain.gcd_dvd_right p q) x)
  · apply (le_rootMultiplicity_iff hg).mpr
    apply EuclideanDomain.dvd_gcd
    · exact (le_rootMultiplicity_iff hp).mp (min_le_left _ _)
    · exact (le_rootMultiplicity_iff hq).mp (min_le_right _ _)

/-- Exact squarefree reduction computed from coefficients. -/
def squarefreeReal (p : Polynomial ℝ) : Polynomial ℝ := p / EuclideanDomain.gcd p p.derivative

lemma squarefreeReal_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) : squarefreeReal p ≠ 0 :=
  polynomial_exact_quotient_ne_zero hp (EuclideanDomain.gcd_dvd_left _ _)

lemma squarefreeReal_mul_factor {p : Polynomial ℝ} (hp : p ≠ 0) :
    EuclideanDomain.gcd p p.derivative * squarefreeReal p = p :=
  polynomial_div_factor hp (EuclideanDomain.gcd_dvd_left _ _)

lemma squarefreeReal_rootMultiplicity {p : Polynomial ℝ} (hp : p ≠ 0) {x : ℝ}
    (hx : p.eval x = 0) : (squarefreeReal p).rootMultiplicity x = 1 := by
  have hd : p.derivative ≠ 0 := by
    intro h
    have hc := eq_C_of_derivative_eq_zero h
    have hz : p.coeff 0 = 0 := by
      have he := congrArg (Polynomial.eval x) hc
      simpa only [eval_C, hx] using he.symm
    exact hp (hc.trans (by rw [hz, map_zero]))
  have hm : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hx
  have hg := rootMultiplicity_gcd_eq_min hp hd x
  rw [derivative_rootMultiplicity_of_root hx, min_eq_right (Nat.sub_le _ _)] at hg
  have hprod := rootMultiplicity_mul (x := x) (p := EuclideanDomain.gcd p p.derivative)
    (q := squarefreeReal p) (by rw [squarefreeReal_mul_factor hp]; exact hp)
  rw [squarefreeReal_mul_factor hp, hg] at hprod
  omega

/-- Squarefree reduction retains exactly the original real root set. -/
theorem squarefreeReal_eval_zero_iff {p : Polynomial ℝ} (hp : p ≠ 0) (x : ℝ) :
    (squarefreeReal p).eval x = 0 ↔ p.eval x = 0 := by
  constructor
  · intro hx
    rw [← squarefreeReal_mul_factor hp, eval_mul, hx, mul_zero]
  · intro hx
    apply (rootMultiplicity_pos (squarefreeReal_ne_zero hp)).mp
    rw [squarefreeReal_rootMultiplicity hp hx]
    exact Nat.zero_lt_one

/-- No real root of the squarefree reduction is a root of its derivative. -/
theorem squarefreeReal_simple {p : Polynomial ℝ} (hp : p ≠ 0) :
    NoCommonRealRoot (squarefreeReal p) (squarefreeReal p).derivative := by
  intro x hx hdx
  have hpx := (squarefreeReal_eval_zero_iff hp x).mp hx
  have hm := squarefreeReal_rootMultiplicity hp hpx
  have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot
    (squarefreeReal_ne_zero hp)).mpr ⟨hx, hdx⟩
  omega

/-- Remove those denominator roots at which the requested weight vanishes. -/
def activeRootPolynomial (p q : Polynomial ℝ) : Polynomial ℝ := p / EuclideanDomain.gcd p q

lemma activeRootPolynomial_ne_zero {p q : Polynomial ℝ} (hp : p ≠ 0) :
    activeRootPolynomial p q ≠ 0 := polynomial_exact_quotient_ne_zero hp (EuclideanDomain.gcd_dvd_left _ _)

lemma activeRootPolynomial_factor {p q : Polynomial ℝ} (hp : p ≠ 0) :
    EuclideanDomain.gcd p q * activeRootPolynomial p q = p := polynomial_div_factor hp (EuclideanDomain.gcd_dvd_left _ _)

lemma noCommonRealRoot_of_factor {p d s : Polynomial ℝ} (heq : d * s = p)
    (h : NoCommonRealRoot p p.derivative) : NoCommonRealRoot s s.derivative := by
  intro x hx hdx
  have hp : p.eval x = 0 := by rw [← heq, eval_mul, hx, mul_zero]
  apply h x hp
  rw [← heq, derivative_mul]
  simp [hx, hdx]

/-- The active polynomial has exactly the nonzero-weight roots of the input. -/
theorem activeRootPolynomial_eval_zero_iff {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p p.derivative) (x : ℝ) :
    (activeRootPolynomial p q).eval x = 0 ↔ p.eval x = 0 ∧ q.eval x ≠ 0 := by
  let d := EuclideanDomain.gcd p q
  let s := activeRootPolynomial p q
  have heq : d * s = p := activeRootPolynomial_factor hp
  constructor
  · intro hs
    change s.eval x = 0 at hs
    have hpx : p.eval x = 0 := by rw [← heq, eval_mul, hs, mul_zero]
    refine ⟨hpx, ?_⟩
    intro hqx
    have hdx : d.eval x = 0 := by
      apply Polynomial.dvd_iff_isRoot.mp
      exact EuclideanDomain.dvd_gcd (Polynomial.dvd_iff_isRoot.mpr hpx) (Polynomial.dvd_iff_isRoot.mpr hqx)
    apply h x hpx
    rw [← heq, derivative_mul]
    simp [hs, hdx]
  · rintro ⟨hpx, hqx⟩
    have hdx : d.eval x ≠ 0 := by
      intro hdx
      obtain ⟨u, hu⟩ := EuclideanDomain.gcd_dvd_right p q
      apply hqx
      rw [hu, eval_mul, hdx, zero_mul]
    have hz : d.eval x * s.eval x = 0 := by rw [← eval_mul, heq]; exact hpx
    exact (mul_eq_zero.mp hz).resolve_left hdx

lemma activeRootPolynomial_simple {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p p.derivative) :
    NoCommonRealRoot (activeRootPolynomial p q) (activeRootPolynomial p q).derivative :=
  noCommonRealRoot_of_factor (activeRootPolynomial_factor hp) h

lemma activeRootPolynomial_weight_nonzero {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p p.derivative) : NoCommonRealRoot (activeRootPolynomial p q) q :=
  fun x hx => ((activeRootPolynomial_eval_zero_iff hp h x).mp hx).2

end QuantumBehaviors.Projection
