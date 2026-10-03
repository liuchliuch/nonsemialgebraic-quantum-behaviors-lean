import QuantumBehaviors.SmallInputs.ThreeMoments

/-! Exact reconstruction from the six moment coordinates; no hidden behavior-model substitution. -/

namespace QuantumBehaviors.SmallInputs

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma strategyBehavior_binary_formula (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (i j : Fin n) (a b : Fin 2) :
    strategyBehavior s (i,j,a,b) =
      if a = 0 then (if b = 0 then 1 - firstMoment s i - firstMoment s j + pairMoment s i j
        else firstMoment s j - pairMoment s i j)
      else (if b = 0 then firstMoment s i - pairMoment s i j else pairMoment s i j) := by
  have hA0 : ∀ i, s.alice i 0 = 1 - s.alice i 1 := by
    intro i
    apply eq_sub_iff_add_eq.mpr
    simpa [Fin.sum_univ_succ] using s.alice_sum i
  have hφ1 : vectorFunctional s.state (1 : H →L[ℂ] H) = 1 := by
    simp only [vectorFunctional_apply, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K,
      s.state_norm, RCLike.ofReal_one, one_pow]
  rw [strategyBehavior_alice_moment s hsync]
  fin_cases a <;> fin_cases b <;>
    simp [hA0, mul_sub, sub_mul, map_sub, map_add, hφ1, Complex.sub_re, Complex.add_re,
      firstMoment, pairMoment] <;> ring

lemma strategyBehavior_sixMoments (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    sixMoments (strategyBehavior s) =
      ![firstMoment s 0, firstMoment s 1, firstMoment s 2,
        pairMoment s 0 1, pairMoment s 0 2, pairMoment s 1 2] := by
  have hproj : ∀ i, s.alice i 1 * s.alice i 1 = s.alice i 1 := fun i =>
    (s.alice_projection i 1).isIdempotentElem.eq
  funext r
  fin_cases r <;> simp [sixMoments, strategyBehavior_alice_moment s hsync, firstMoment, pairMoment, hproj]

lemma moment_array_first {r t : Fin 3 → ℝ} {w v : Fin 3 → Fin 3 → ℝ}
    (he : (![r 0,r 1,r 2,w 0 1,w 0 2,w 1 2] : Fin 6 → ℝ) = ![t 0,t 1,t 2,v 0 1,v 0 2,v 1 2]) : r = t := by
  funext i
  fin_cases i
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 2

lemma moment_array_pairs {r t : Fin 3 → ℝ} {w v : Fin 3 → Fin 3 → ℝ}
    (hw : ∀ i j, w i j = w j i) (hv : ∀ i j, v i j = v j i)
    (hwd : ∀ i, w i i = r i) (hvd : ∀ i, v i i = t i)
    (he : (![r 0,r 1,r 2,w 0 1,w 0 2,w 1 2] : Fin 6 → ℝ) = ![t 0,t 1,t 2,v 0 1,v 0 2,v 1 2]) : w = v := by
  have hr := moment_array_first he
  have h01 : w 0 1 = v 0 1 := congrFun he 3
  have h02 : w 0 2 = v 0 2 := congrFun he 4
  have h12 : w 1 2 = v 1 2 := congrFun he 5
  funext i j
  fin_cases i <;> fin_cases j
  · rw [hwd, hvd, hr]
  · exact h01
  · exact h02
  · exact (hw 1 0).trans (h01.trans (hv 1 0).symm)
  · rw [hwd, hvd, hr]
  · exact h12
  · exact (hw 2 0).trans (h02.trans (hv 2 0).symm)
  · exact (hw 2 1).trans (h12.trans (hv 2 1).symm)
  · rw [hwd, hvd, hr]

/-- Six moments determine the entire genuine synchronous commuting behavior. -/
theorem sixMoments_injective_on_synchronous : Set.InjOn sixMoments (Scenarios.synchronousSet 3 .qc) := by
  rintro p ⟨⟨H,hN,hI,hC,s,hr⟩,hp⟩ q ⟨⟨G,gN,gI,gC,t,ht⟩,hq⟩ he
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  letI : NormedAddCommGroup G := gN
  letI : InnerProductSpace ℂ G := gI
  letI : CompleteSpace G := gC
  have hs := synchronous_vector_outcome s hr hp
  have ht' := synchronous_vector_outcome t ht hq
  rw [← strategyBehavior_eq hr, ← strategyBehavior_eq ht] at he ⊢
  rw [strategyBehavior_sixMoments s hs, strategyBehavior_sixMoments t ht'] at he
  have hfirst := moment_array_first he
  have hpairs := moment_array_pairs (pairMoment_symm s hs) (pairMoment_symm t ht')
    (pairMoment_diag s) (pairMoment_diag t) he
  funext x
  rcases x with ⟨i,j,a,b⟩
  rw [strategyBehavior_binary_formula s hs, strategyBehavior_binary_formula t ht', hfirst, hpairs]

end QuantumBehaviors.SmallInputs
