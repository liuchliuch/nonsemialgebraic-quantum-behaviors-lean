import QuantumBehaviors.Projection.EliminateRoots

/-!
# One-real-variable elimination

This file assembles the proved polynomial sampling theorem, the uniform Tarski-query
algorithm and finite sign-formula compilation. Its output is actual finite quantifier-free
polynomial-sign syntax with arbitrary real coefficients.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Polynomial Set
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype α] [DecidableEq α]

/-- Sampling with finite root sets, including the constant-product/zero-derivative case. -/
theorem polynomial_finite_formula_sampling (p : α → Polynomial ℝ) (φ : SignFormula α) :
    (∃ t : ℝ, φ.eval (fun i => SignType.sign ((p i).eval t)) = true) ↔
    φ.eval (fun i => SignType.sign ((p i).leadingCoeff * (-1 : ℝ) ^ (p i).natDegree)) = true ∨
    φ.eval (fun i => SignType.sign (p i).leadingCoeff) = true ∨
    (∃ t ∈ (rootProduct p).roots.toFinset, φ.eval (fun i => SignType.sign ((p i).eval t)) = true) ∨
    (∃ t ∈ (rootProduct p).derivative.roots.toFinset,
      φ.eval (fun i => SignType.sign ((p i).eval t)) = true) := by
  rw [polynomial_formula_sampling]
  constructor
  · rintro (h | h | ⟨t, ht | ht, hφ⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨t, Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (rootProduct_ne_zero p)).mpr ht), hφ⟩))
    · by_cases hd : (rootProduct p).derivative = 0
      · have hc := eq_C_of_derivative_eq_zero hd
        have hn : ∀ u : ℝ, (rootProduct p).eval u ≠ 0 := by
          intro u hu
          have hcz : (rootProduct p).coeff 0 = 0 := by
            have he := congrArg (Polynomial.eval u) hc
            simpa only [eval_C, hu] using he.symm
          exact rootProduct_ne_zero p (hc.trans (by rw [hcz, map_zero]))
        have htop : ∀ᶠ u in atTop, ∀ i, SignType.sign ((p i).eval u) =
            SignType.sign (p i).leadingCoeff :=
          Filter.eventually_all.mpr fun i => polynomial_eventually_sign_atTop (p i)
        obtain ⟨u, hu⟩ := htop.exists
        have heq : (fun i => SignType.sign (p i).leadingCoeff) =
            (fun i => SignType.sign ((p i).eval t)) := by
          funext i
          exact (hu i).symm.trans (polynomial_family_sign_const_on p isPreconnected_univ
            (fun x _ => hn x) (Set.mem_univ u) (Set.mem_univ t) i)
        exact Or.inr (Or.inl (by rw [heq]; exact hφ))
      · exact Or.inr (Or.inr (Or.inr ⟨t, Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hd).mpr ht), hφ⟩))
  · rintro (h | h | ⟨t, ht, hφ⟩ | ⟨t, ht, hφ⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨t, Or.inl
        (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ht)), hφ⟩)
    · exact Or.inr (Or.inr ⟨t, Or.inr
        (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ht)), hφ⟩)

lemma RationalPolynomialMap.rootProduct (Q : α → (ι → ℝ) → Polynomial ℝ)
    (hQ : ∀ i, RationalPolynomialMap (Q i)) :
    RationalPolynomialMap (fun x => Projection.rootProduct (fun i => Q i x)) := by
  classical
  apply RationalPolynomialMap.finset_prod
  intro i hi
  convert (RationalPolynomialMap.const (ι := ι) 1).ite (hQ i).isSemialgebraic_zero (hQ i) using 1
  funext x
  by_cases hx : Q i x = 0 <;> simp [Set.mem_setOf_eq, hx]

/-- Genuine elimination for an arbitrary finite family with coefficient-rational parameter maps. -/
theorem isSemialgebraic_exists_eval (Q : α → (ι → ℝ) → Polynomial ℝ)
    (hQ : ∀ i, RationalPolynomialMap (Q i)) (φ : SignFormula α) :
    IsSemialgebraic {x : ι → ℝ | ∃ t : ℝ,
      φ.eval (fun i => SignType.sign ((Q i x).eval t)) = true} := by
  have hneg := isSemialgebraic_rational_formula
    (fun i x => (Q i x).leadingCoeff * (-1 : ℝ) ^ (Q i x).natDegree)
    (fun i => (hQ i).negInfCoeff) φ
  have hpos := isSemialgebraic_rational_formula
    (fun i x => (Q i x).leadingCoeff) (fun i => (hQ i).leadingCoeff) φ
  let P := fun x => rootProduct (fun i => Q i x)
  have hP : RationalPolynomialMap P := RationalPolynomialMap.rootProduct Q hQ
  have hroot := isSemialgebraic_root_formula P Q hP hQ φ
  have hderiv := isSemialgebraic_root_formula (fun x => (P x).derivative) Q hP.derivative hQ φ
  convert hneg.union (hpos.union (hroot.union hderiv)) using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact polynomial_finite_formula_sampling (fun i => Q i x) φ

/-- Elimination for actual polynomial coefficient families. -/
theorem isSemialgebraic_exists_polynomial (Q : α → Polynomial (MvPolynomial ι ℝ))
    (φ : SignFormula α) :
    IsSemialgebraic {x : ι → ℝ | ∃ t : ℝ,
      φ.eval (fun i => SignType.sign ((Q i).map (MvPolynomial.eval x) |>.eval t)) = true} :=
  isSemialgebraic_exists_eval (fun i x => (Q i).map (MvPolynomial.eval x))
    (fun i => RationalPolynomialMap.ofPolynomial (Q i)) φ

/-- The extracted, genuinely quantifier-free finite polynomial-sign formula. -/
def eliminatePolynomialExists (Q : α → Polynomial (MvPolynomial ι ℝ))
    (φ : SignFormula α) : PolynomialSignFormula ι :=
  (isSemialgebraic_iff_formula.mp (isSemialgebraic_exists_polynomial Q φ)).choose

/-- Exact correctness of the extracted finite formula, with arbitrary real coefficients. -/
theorem eliminatePolynomialExists_correct (Q : α → Polynomial (MvPolynomial ι ℝ))
    (φ : SignFormula α) (x : ι → ℝ) :
    (eliminatePolynomialExists Q φ).realize x = true ↔
      ∃ t : ℝ, φ.eval (fun i => SignType.sign
        ((Q i).map (MvPolynomial.eval x) |>.eval t)) = true :=
  ((isSemialgebraic_iff_formula.mp (isSemialgebraic_exists_polynomial Q φ)).choose_spec x).symm

end QuantumBehaviors.Projection
