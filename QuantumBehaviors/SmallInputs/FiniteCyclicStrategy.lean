import QuantumBehaviors.SmallInputs.CyclicStrategy
import QuantumBehaviors.SmallInputs.ClosedStationaryAlgebra

/-! Finite-dimensionality of the cyclic strategy from the proved stationary algebra bound. -/

namespace QuantumBehaviors.SmallInputs

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def algebraEvaluation (D : Subalgebra ℂ (H →L[ℂ] H)) (ψ : H) : D →ₗ[ℂ] H where
  toFun X := X.1 ψ
  map_add' X Y := rfl
  map_smul' c X := rfl

lemma alice_mem_algebra (s : Scenarios.CommutingStrategy n n 2 2 H) (i : Fin n) (a : Fin 2) :
    s.alice i a ∈ aliceAlgebra s := by
  have h1 : s.alice i 1 ∈ aliceAlgebra s := Algebra.subset_adjoin ⟨i,rfl⟩
  fin_cases a
  · have hA0 : s.alice i 0 = 1 - s.alice i 1 := by
      have he : s.alice i 0 + s.alice i 1 = 1 := by simpa [Fin.sum_univ_succ] using s.alice_sum i
      exact eq_sub_iff_add_eq.mpr he
    change s.alice i 0 ∈ aliceAlgebra s
    rw [hA0]
    exact (aliceAlgebra s).sub_mem (aliceAlgebra s).one_mem h1
  · exact h1

lemma aliceAlgebra_commute_bob_outcome (s : Scenarios.CommutingStrategy n n 2 2 H)
    {X : H →L[ℂ] H} (hX : X ∈ aliceAlgebra s) (j : Fin n) (b : Fin 2) : Commute X (s.bob j b) := by
  apply Commute.symm
  apply commute_adjoin (K := ℂ) _ X hX
  rintro P ⟨i,rfl⟩
  exact (s.cross_commute i j 1 b).symm

lemma cyclicWord_mem_evaluation_range (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (w : List (Fin n × Fin 2)) :
    cyclicWord (bobFamily s) w s.state ∈ (algebraEvaluation (aliceAlgebra s) s.state).range := by
  induction w with
  | nil => exact ⟨1,rfl⟩
  | cons ia w ih =>
    obtain ⟨X,hX⟩ := ih
    refine ⟨X * ⟨s.alice ia.1 ia.2, alice_mem_algebra s ia.1 ia.2⟩, ?_⟩
    change X.1 (s.alice ia.1 ia.2 s.state) = s.bob ia.1 ia.2 (cyclicWord (bobFamily s) w s.state)
    rw [hsync]
    have he := congrArg (fun T : H →L[ℂ] H => T s.state)
      (aliceAlgebra_commute_bob_outcome s X.property ia.1 ia.2).eq
    change X.1 (s.bob ia.1 ia.2 s.state) = s.bob ia.1 ia.2 (X.1 s.state) at he
    rw [he]
    exact congrArg (s.bob ia.1 ia.2) hX

lemma cyclicSpace_le_evaluation_range (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    [FiniteDimensional ℂ (aliceAlgebra s)] :
    strategyCyclicSpace s ≤ (algebraEvaluation (aliceAlgebra s) s.state).range := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    exact cyclicWord_mem_evaluation_range s hsync w
  · exact Submodule.closed_of_finiteDimensional _

/-- A finite Alice algebra produces a finite, complete cyclic Hilbert space with
no increase in its vector-space dimension. -/
theorem finite_cyclic_strategy (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    [FiniteDimensional ℂ (aliceAlgebra s)] :
    FiniteDimensional ℂ (strategyCyclicSpace s) ∧
      Module.finrank ℂ (strategyCyclicSpace s) ≤ Module.finrank ℂ (aliceAlgebra s) := by
  have hle := cyclicSpace_le_evaluation_range s hsync
  exact ⟨Submodule.finiteDimensional_of_le hle,
    (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le _)⟩

lemma three_alice_algebra (s : Scenarios.CommutingStrategy 3 3 2 2 H) :
    aliceAlgebra s = Algebra.adjoin ℂ ({s.alice 0 1, s.alice 1 1, s.alice 2 1} : Set (H →L[ℂ] H)) := by
  change Algebra.adjoin ℂ _ = Algebra.adjoin ℂ _
  apply congrArg (Algebra.adjoin ℂ)
  ext X
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- A genuine stationary three-input commuting strategy has a cyclic realization
on a Hilbert space of dimension at most twelve. -/
theorem stationary_strategy_finite_cyclic (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : Commute (s.alice 0 1) (a • s.alice 1 1 + b • s.alice 2 1))
    (h₂ : Commute (s.alice 1 1) (a • s.alice 0 1 + s.alice 2 1)) :
    FiniteDimensional ℂ (strategyCyclicSpace s) ∧ Module.finrank ℂ (strategyCyclicSpace s) ≤ 12 := by
  obtain ⟨hf, hd⟩ := russell_adjoin_finiteDimensional ha hb
    (s.alice_projection 0 1).isIdempotentElem (s.alice_projection 1 1).isIdempotentElem
    (s.alice_projection 2 1).isIdempotentElem h₁ h₂
  rw [← three_alice_algebra s] at hf hd
  letI : FiniteDimensional ℂ (aliceAlgebra s) := hf
  obtain ⟨hK,hKd⟩ := finite_cyclic_strategy s hsync
  exact ⟨hK,hKd.trans hd⟩

lemma cyclicStrategy_synchronized (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    ∀ i a, (cyclicStrategy s hsync).alice i a (cyclicStrategy s hsync).state =
      (cyclicStrategy s hsync).bob i a (cyclicStrategy s hsync).state := by
  intro i a
  apply Subtype.ext
  exact hsync i a

lemma cyclicStrategy_word_vector (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (w : List (Fin n × Fin 2)) :
    cyclicWord (bobFamily (cyclicStrategy s hsync)) w (cyclicStrategy s hsync).state =
      cyclicWordVector (bobFamily s) s.state w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [cyclicWord_cons, ContinuousLinearMap.mul_apply, ih, cyclicWordVector_cons]
    rfl

/-- Evaluation at the cyclic vector is injective on the actual Alice algebra. -/
theorem cyclicStrategy_evaluation_injective (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    Function.Injective (algebraEvaluation (aliceAlgebra (cyclicStrategy s hsync))
      (cyclicStrategy s hsync).state) := by
  intro X Y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply cyclicStrategy_commutant_faithful s hsync
    ((aliceAlgebra (cyclicStrategy s hsync)).sub_mem X.property Y.property)
  change X.1 (cyclicStrategy s hsync).state - Y.1 (cyclicStrategy s hsync).state = 0
  exact sub_eq_zero.mpr he

/-- In finite dimension, the dense cyclic evaluation range is all of the Hilbert space. -/
theorem cyclicStrategy_evaluation_surjective (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    [FiniteDimensional ℂ (aliceAlgebra (cyclicStrategy s hsync))] :
    Function.Surjective (algebraEvaluation (aliceAlgebra (cyclicStrategy s hsync))
      (cyclicStrategy s hsync).state) := by
  let K := strategyCyclicSpace s
  let E := algebraEvaluation (aliceAlgebra (cyclicStrategy s hsync)) (cyclicStrategy s hsync).state
  let M := E.range
  let N := M.comap K.orthogonalProjection.toLinearMap
  have hMclosed : IsClosed (M : Set K) := Submodule.closed_of_finiteDimensional M
  have hNclosed : IsClosed (N : Set H) := hMclosed.preimage K.orthogonalProjection.continuous
  have hwords : ∀ w : List (Fin n × Fin 2), cyclicWordVector (bobFamily s) s.state w ∈ M := by
    intro w
    rw [← cyclicStrategy_word_vector s hsync w]
    exact cyclicWord_mem_evaluation_range (cyclicStrategy s hsync) (cyclicStrategy_synchronized s hsync) w
  have hspan : cyclicSpanAny (bobFamily s) s.state ≤ N := by
    apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    change K.orthogonalProjection (cyclicWord (bobFamily s) w s.state) ∈ M
    have he : K.orthogonalProjection (cyclicWord (bobFamily s) w s.state) =
        cyclicWordVector (bobFamily s) s.state w := by
      apply Subtype.ext
      exact K.starProjection_eq_self_iff.mpr (cyclicWord_mem (bobFamily s) s.state w)
    rw [he]
    exact hwords w
  have hKN : K ≤ N := Submodule.topologicalClosure_minimal _ hspan hNclosed
  intro x
  have hx := hKN x.property
  change K.orthogonalProjection (x : H) ∈ M at hx
  have he : K.orthogonalProjection (x : H) = x := by
    apply Subtype.ext
    exact K.starProjection_eq_self_iff.mpr x.property
  rw [he] at hx
  exact hx

/-- Exact finite Hilbert-algebra identification used in the tensor dilation. -/
theorem cyclicStrategy_evaluation_bijective (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    [FiniteDimensional ℂ (aliceAlgebra (cyclicStrategy s hsync))] :
    Function.Bijective (algebraEvaluation (aliceAlgebra (cyclicStrategy s hsync))
      (cyclicStrategy s hsync).state) :=
  ⟨cyclicStrategy_evaluation_injective s hsync, cyclicStrategy_evaluation_surjective s hsync⟩

end QuantumBehaviors.SmallInputs
