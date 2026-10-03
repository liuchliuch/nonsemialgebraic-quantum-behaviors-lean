import QuantumBehaviors.NPA.Definitions
import QuantumBehaviors.NPA.Words
import QuantumBehaviors.AlmostQuantum.Physical

/-! Actual finite NPA word-moment certificates, with proper binary behavior probabilities. -/
namespace QuantumBehaviors.NPA
open Matrix
open scoped BigOperators ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def letters (s : CommutingStrategy H) : Letter → H →L[ℂ] H := Sum.elim s.alice s.bob

lemma letters_projection (s : CommutingStrategy H) (c : Letter) : IsStarProjection (letters s c) := by
  cases c with
  | inl i => exact s.alice_projection i
  | inr j => exact s.bob_projection j

lemma wordEval_rel (s : CommutingStrategy H) {u v : Word} (h : WordRel u v) :
    wordEval (letters s) u=wordEval (letters s) v :=
  h.eval_eq (letters s) (fun c => (letters_projection s c).isIdempotentElem.eq) (fun i j => (s.cross_commute i j).eq)

lemma word_inner (s : CommutingStrategy H) (u v : Word) :
    inner ℂ (wordEval (letters s) u s.state) (wordEval (letters s) v s.state)=
      inner ℂ s.state (wordEval (letters s) (u.reverse++v) s.state) := by
  rw [wordEval_append,wordEval_reverse (letters s) (fun c => (letters_projection s c).isSelfAdjoint.star_eq)]
  change inner ℂ (wordEval (letters s) u s.state) (wordEval (letters s) v s.state)=
    inner ℂ s.state ((ContinuousLinearMap.adjoint (wordEval (letters s) u)) (wordEval (letters s) v s.state))
  exact ((wordEval (letters s) u).adjoint_inner_right _ _).symm

noncomputable def quantumCertificate (s : CommutingStrategy H) {p : Behavior} (hp : s.realizes p) (k : ℕ) : Certificate k p where
  gram := Matrix.gram ℂ (fun w : BoundedWord (k+1) => wordEval (letters s) w.val s.state)
  positive := Matrix.posSemidef_gram ℂ _
  normalized := by simp [Matrix.gram_apply,emptyIndex,inner_self_eq_norm_sq_to_K,s.state_norm]
  relations := by
    intro u v r t h
    simp only [Matrix.gram_apply,word_inner,wordEval_rel s h]
  born := by
    intro i j a b
    rw [hp]
    have hAB : inner ℂ (s.alice i s.state) (s.bob j s.state)=inner ℂ s.state (s.alice i (s.bob j s.state)) :=
      AlmostQuantum.selfadjoint_inner_left _ (s.alice_projection i).isSelfAdjoint _ _
    cases a <;> cases b <;>
      simp [bornValue,Matrix.gram_apply,emptyIndex,letterIndex,letters,effect,ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.sub_apply,map_sub,inner_sub_right,hAB,s.state_norm]
    ring
  nonnegative := by
    let aq : AlmostQuantum.Strategy H := {
      state := s.state,state_norm := s.state_norm,alice := s.alice,bob := s.bob
      alice_projection := s.alice_projection,bob_projection := s.bob_projection
      cross_on_state := fun i j => congrArg (fun T : H →L[ℂ] H => T s.state) (s.cross_commute i j).eq }
    exact aq.nonnegative hp

/-- Every actual arbitrary-Hilbert commuting behavior passes every finite NPA level. -/
theorem cqc_subset_level (k : ℕ) : Cqc ⊆ level k := by
  rintro p ⟨H,hN,hI,hC,s,hp⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  exact ⟨quantumCertificate s hp k⟩

noncomputable def Certificate.restrict {k l : ℕ} (hkl : k ≤ l) {p : Behavior} (c : Certificate l p) : Certificate k p where
  gram := c.gram.submatrix (fun w => ⟨w.val,w.property.trans (Nat.add_le_add_right hkl 1)⟩)
    (fun w => ⟨w.val,w.property.trans (Nat.add_le_add_right hkl 1)⟩)
  positive := c.positive.submatrix _
  normalized := c.normalized
  relations := fun u v r s h => c.relations _ _ _ _ h
  born := by
    intro i j a b
    simpa only [bornValue,Matrix.submatrix_apply,emptyIndex,letterIndex] using c.born i j a b
  nonnegative := c.nonnegative

theorem level_antitone : Antitone level := by
  intro k l hkl p hp
  obtain ⟨c⟩ := hp
  exact ⟨c.restrict hkl⟩

lemma Certificate.probabilities_normalized {k : ℕ} {p : Behavior} (c : Certificate k p) : Normalized p := by
  intro i j
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_one]
  simp_rw [c.born]
  simp [bornValue]

lemma Certificate.probabilities_nonsignaling {k : ℕ} {p : Behavior} (c : Certificate k p) : Nonsignaling p := by
  constructor
  · intro i j t a
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum]
    simp_rw [c.born]
    cases a <;> simp [bornValue]
  · intro i j t b
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum]
    simp_rw [c.born]
    cases b <;> simp [bornValue] <;> ring

end QuantumBehaviors.NPA
