import QuantumBehaviors.SmallInputs.ExponentialTransfer

/-! Genuine synchronous commuting strategies under a mirrored one-input unitary variation. -/

namespace QuantumBehaviors.SmallInputs

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commute_star_left_of_selfadjoint {U P : H →L[ℂ] H} (h : Commute U P)
    (hP : IsSelfAdjoint P) : Commute (star U) P := by
  simpa only [hP.star_eq] using h.star_star

set_option maxHeartbeats 800000 in
noncomputable def conjugateStrategy (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n)
    (U V : unitary (H →L[ℂ] H))
    (hUB : ∀ j b, Commute (U : H →L[ℂ] H) (s.bob j b))
    (hVA : ∀ i a, Commute (V : H →L[ℂ] H) (s.alice i a))
    (hUV : Commute (U : H →L[ℂ] H) (V : H →L[ℂ] H))
    (hUVs : Commute (U : H →L[ℂ] H) (star (V : H →L[ℂ] H))) :
    Scenarios.CommutingStrategy n n 2 2 H where
  state := s.state
  state_norm := s.state_norm
  alice i a := if i = k then Unitary.conjStarAlgAut ℂ _ U (s.alice i a) else s.alice i a
  bob j b := if j = k then Unitary.conjStarAlgAut ℂ _ (star V) (s.bob j b) else s.bob j b
  alice_projection i a := by
    split_ifs
    · exact (s.alice_projection i a).map (Unitary.conjStarAlgAut ℂ _ U)
    · exact s.alice_projection i a
  bob_projection j b := by
    split_ifs
    · exact (s.bob_projection j b).map (Unitary.conjStarAlgAut ℂ _ (star V))
    · exact s.bob_projection j b
  alice_sum i := by
    by_cases hi : i = k
    · simp only [hi, ↓reduceIte, ← map_sum, s.alice_sum, map_one]
    · simpa only [hi, ↓reduceIte] using s.alice_sum i
  bob_sum j := by
    by_cases hj : j = k
    · simp only [hj, ↓reduceIte, ← map_sum, s.bob_sum, map_one]
    · simpa only [hj, ↓reduceIte] using s.bob_sum j
  cross_commute i j a b := by
    have hUsB := commute_star_left_of_selfadjoint (hUB j b) (s.bob_projection j b).isSelfAdjoint
    have hVsA := commute_star_left_of_selfadjoint (hVA i a) (s.alice_projection i a).isSelfAdjoint
    have hUsV : Commute (star (U : H →L[ℂ] H)) (V : H →L[ℂ] H) := by
      simpa only [star_star] using hUVs.star_star
    by_cases hi : i = k <;> by_cases hj : j = k
    · simp only [hi, hj, ↓reduceIte, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
      simpa only [hi, hj] using (((hUVs.mul_right (hUB j b)).mul_right hUV).mul_left
        ((hVsA.symm.mul_right (s.cross_commute i j a b)).mul_right (hVA i a).symm)).mul_left
          ((hUV.star_star.mul_right hUsB).mul_right hUsV)
    · simp only [hi, hj, ↓reduceIte, Unitary.conjStarAlgAut_apply, Unitary.coe_star]
      simpa only [hi, hj] using ((hUB j b).mul_left (s.cross_commute i j a b)).mul_left hUsB
    · simp only [hi, hj, ↓reduceIte, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
      simpa only [hi, hj] using (hVsA.symm.mul_right (s.cross_commute i j a b)).mul_right (hVA i a).symm
    · simpa only [hi, hj, ↓reduceIte] using s.cross_commute i j a b

lemma conjugateStrategy_synchronized (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n)
    (U V : unitary (H →L[ℂ] H))
    (hUB : ∀ j b, Commute (U : H →L[ℂ] H) (s.bob j b))
    (hVA : ∀ i a, Commute (V : H →L[ℂ] H) (s.alice i a))
    (hUV : Commute (U : H →L[ℂ] H) (V : H →L[ℂ] H))
    (hUVs : Commute (U : H →L[ℂ] H) (star (V : H →L[ℂ] H)))
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (hψ : (U : H →L[ℂ] H) s.state = (V : H →L[ℂ] H) s.state)
    (hψs : (star (U : H →L[ℂ] H)) s.state = (star (V : H →L[ℂ] H)) s.state) :
    ∀ i a, (conjugateStrategy s k U V hUB hVA hUV hUVs).alice i a s.state =
      (conjugateStrategy s k U V hUB hVA hUV hUVs).bob i a s.state := by
  intro i a
  by_cases hi : i = k
  · subst i
    simp only [conjugateStrategy, ↓reduceIte, Unitary.conjStarAlgAut_apply,
      Unitary.coe_star, star_star, ContinuousLinearMap.mul_apply]
    have hVsA := commute_star_left_of_selfadjoint (hVA k a) (s.alice_projection k a).isSelfAdjoint
    have he₁ := congrArg (fun T : H →L[ℂ] H => T s.state) hVsA.symm.eq
    have he₂ := congrArg (fun T : H →L[ℂ] H => T (s.alice k a s.state)) hUVs.eq
    have he₃ := congrArg (fun T : H →L[ℂ] H => T s.state) (hUB k a).eq
    simp only [ContinuousLinearMap.mul_apply] at he₁ he₂ he₃
    rw [hψs, he₁, he₂, hsync, he₃, hψ]
  · simpa only [conjugateStrategy, hi, ↓reduceIte] using hsync i a

end QuantumBehaviors.SmallInputs
