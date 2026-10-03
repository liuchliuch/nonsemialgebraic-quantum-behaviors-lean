import QuantumBehaviors.SpectralClassification

/-!
# Necessity in the full scalar classification

The interval `(1,2)` theorem, positivity, and complementing all four
projections give the complete set of possible scalars.  Existence at these
parameters is supplied separately by the finite-dimensional construction.
-/

namespace QuantumBehaviors

/-- The full set of scalars permitted for a sum of four orthogonal projections.
The last disjunct is the upper discrete branch `2 + 2/m`. -/
def SigmaFour : Set ℝ := {α | α = 0 ∨ α = 1 ∨ α = 2 ∨ α = 3 ∨ α = 4 ∨
  Allowed α ∨ Allowed (4 - α)}

/-- The complemented lower branch is exactly the upper branch printed in the
paper's scalar classification. -/
theorem allowed_complement_iff (α : ℝ) :
    Allowed (4 - α) ↔ ∃ m : ℕ, 3 ≤ m ∧ α = 2 + 2 / (m : ℝ) := by
  constructor
  · rintro ⟨m, hm, heq⟩
    refine ⟨m, hm, ?_⟩
    unfold alpha at heq
    linarith
  · rintro ⟨m, hm, heq⟩
    refine ⟨m, hm, ?_⟩
    unfold alpha
    linarith

/-- The scalar set in literal numerical form. -/
theorem mem_sigmaFour_iff (α : ℝ) :
    α ∈ SigmaFour ↔ α = 0 ∨ α = 1 ∨ α = 2 ∨ α = 3 ∨ α = 4 ∨
      (∃ m : ℕ, 3 ≤ m ∧ α = 2 - 2 / (m : ℝ)) ∨
      (∃ m : ℕ, 3 ≤ m ∧ α = 2 + 2 / (m : ℝ)) := by
  simp only [SigmaFour, Set.mem_setOf_eq]
  rw [allowed_complement_iff]
  rfl

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

/-- A projection bounded above by a scalar strictly below one is zero. -/
theorem projection_eq_zero_of_scalar_bound {P : A} (hP : IsStarProjection P)
    {α : ℝ} (hα : α < 1) (hbound : 0 ≤ algebraMap ℝ A α - P) : P = 0 := by
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) P ?_ hP.isSelfAdjoint
  intro x hx
  have hx01 := hP.isIdempotentElem.spectrum_subset ℝ hx
  rcases Set.mem_insert_iff.mp hx01 with hxzero | hxone
  · exact Set.mem_singleton_iff.mpr hxzero
  · have hxs : x = 1 := Set.mem_singleton_iff.mp hxone
    have hnonneg := spectrum_nonneg_of_nonneg hbound
      ((spectrum_scalar_sub_iff P α x).mpr hx)
    rw [hxs] at hnonneg
    linarith

/-- A sum of four projections cannot be a scalar strictly between zero and one;
in fact every scalar sum below one is zero. -/
theorem four_projection_scalar_lt_one_eq_zero {P Q R S : A}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    {α : ℝ} (hsum : P + Q + R + S = algebraMap ℝ A α)
    (hα : α < 1) : α = 0 := by
  have hPzero : P = 0 := projection_eq_zero_of_scalar_bound hP hα (by
    rw [← hsum]
    convert add_nonneg hQ.nonneg (add_nonneg hR.nonneg hS.nonneg) using 1 <;> abel)
  have hQzero : Q = 0 := projection_eq_zero_of_scalar_bound hQ hα (by
    rw [← hsum]
    convert add_nonneg hP.nonneg (add_nonneg hR.nonneg hS.nonneg) using 1 <;> abel)
  have hRzero : R = 0 := projection_eq_zero_of_scalar_bound hR hα (by
    rw [← hsum]
    convert add_nonneg hP.nonneg (add_nonneg hQ.nonneg hS.nonneg) using 1 <;> abel)
  have hSzero : S = 0 := projection_eq_zero_of_scalar_bound hS hα (by
    rw [← hsum]
    convert add_nonneg hP.nonneg (add_nonneg hQ.nonneg hR.nonneg) using 1 <;> abel)
  apply (algebraMap ℝ A).injective
  simpa only [hPzero, hQzero, hRzero, hSzero, add_zero, map_zero] using hsum.symm

/-- Complementing four projections reflects the scalar sum about two. -/
theorem four_projections_complement_sum {P Q R S : A} {α : ℝ}
    (hsum : P + Q + R + S = algebraMap ℝ A α) :
    (1 - P) + (1 - Q) + (1 - R) + (1 - S) = algebraMap ℝ A (4 - α) := by
  rw [map_sub, map_ofNat, ← hsum]
  have hfour : (4 : A) = 1 + 1 + 1 + 1 := by norm_num
  rw [hfour]
  abel

/-- Full necessity in the scalar classification, with no dimension restriction
and no appeal to an external classification theorem. -/
theorem four_projections_mem_sigmaFour_cstar {P Q R S : A}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    {α : ℝ} (hsum : P + Q + R + S = algebraMap ℝ A α) : α ∈ SigmaFour := by
  change α = 0 ∨ α = 1 ∨ α = 2 ∨ α = 3 ∨ α = 4 ∨ Allowed α ∨ Allowed (4 - α)
  by_cases hltone : α < 1
  · exact Or.inl (four_projection_scalar_lt_one_eq_zero hP hQ hR hS hsum hltone)
  by_cases heqone : α = 1
  · exact Or.inr (Or.inl heqone)
  have hgtone : 1 < α := lt_of_le_of_ne (le_of_not_gt hltone) (Ne.symm heqone)
  by_cases hlttwo : α < 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (four_projections_allowed_cstar hP hQ hR hS hsum hgtone hlttwo))))))
  by_cases heqtwo : α = 2
  · exact Or.inr (Or.inr (Or.inl heqtwo))
  have hgttwo : 2 < α := lt_of_le_of_ne (le_of_not_gt hlttwo) (Ne.symm heqtwo)
  have hcomp := four_projections_complement_sum hsum
  by_cases hcompltone : 4 - α < 1
  · have hzero := four_projection_scalar_lt_one_eq_zero
      hP.one_sub hQ.one_sub hR.one_sub hS.one_sub hcomp hcompltone
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
  by_cases hcompeqone : 4 - α = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
  have hcompgtone : 1 < 4 - α :=
    lt_of_le_of_ne (le_of_not_gt hcompltone) (Ne.symm hcompeqone)
  have hcomplttwo : 4 - α < 2 := by linarith
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (four_projections_allowed_cstar hP.one_sub hQ.one_sub hR.one_sub hS.one_sub
      hcomp hcompgtone hcomplttwo))))))

end CStarAlgebra

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Necessity in the full KRS scalar set for bounded projections on any nonzero
complex Hilbert space. -/
theorem four_projections_mem_sigmaFour {P Q R S : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    {α : ℝ} (hsum : P + Q + R + S = algebraMap ℝ (H →L[ℂ] H) α) :
    α ∈ SigmaFour := four_projections_mem_sigmaFour_cstar hP hQ hR hS hsum

end Hilbert

end QuantumBehaviors
