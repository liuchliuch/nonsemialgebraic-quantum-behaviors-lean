import QuantumBehaviors.NPA.Models

/-! Removing duplicate syntactic word rows does not change NPA feasibility. -/
namespace QuantumBehaviors.NPA
open Matrix
open scoped ComplexOrder

instance wordSetoid (n : ℕ) : Setoid (BoundedWord n) where
  r u v := WordRel u.val v.val
  iseqv := ⟨fun _ => .refl _,fun h => h.symm,fun h g => h.trans g⟩

/-- Standard word classes represented by words of length at most n. -/
def ReducedWord (n : ℕ) := Quotient (wordSetoid n)
instance (n : ℕ) : Finite (ReducedWord n) := Quotient.finite _
noncomputable instance (n : ℕ) : Fintype (ReducedWord n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : DecidableEq (ReducedWord n) := Classical.decEq _

def reduceWord {n : ℕ} (w : BoundedWord n) : ReducedWord n := Quotient.mk _ w
noncomputable def chooseWord {n : ℕ} (w : ReducedWord n) : BoundedWord n := Quotient.out w

lemma chooseWord_rel {n : ℕ} (w : BoundedWord n) : WordRel (chooseWord (reduceWord w)).val w.val :=
  Quotient.exact (Quotient.out_eq (reduceWord w))

variable {k : ℕ} {p : Behavior}

lemma Certificate.gram_congr (c : Certificate k p) {u v r s : BoundedWord (k+1)}
    (hu : WordRel u.val r.val) (hv : WordRel v.val s.val) : c.gram u v=c.gram r s :=
  c.relations _ _ _ _ (hu.reverse.append hv)

/-- The matrix on distinct word classes is a genuine PSD principal submatrix. -/
noncomputable def Certificate.reducedGram (c : Certificate k p) :
    Matrix (ReducedWord (k+1)) (ReducedWord (k+1)) ℂ := c.gram.submatrix chooseWord chooseWord

lemma Certificate.reducedGram_positive (c : Certificate k p) : c.reducedGram.PosSemidef :=
  c.positive.submatrix chooseWord

/-- Pulling the reduced matrix back recovers every entry, including all duplicate rows. -/
lemma Certificate.reducedGram_pullback (c : Certificate k p) :
    c.reducedGram.submatrix reduceWord reduceWord=c.gram := by
  apply Matrix.ext
  intro u v
  exact c.gram_congr (chooseWord_rel u) (chooseWord_rel v)

/-- PSD is unchanged by quotienting duplicate rows whenever the word identities hold. -/
lemma positive_iff_reduced {n : ℕ} (Γ : Matrix (BoundedWord n) (BoundedWord n) ℂ)
    (hΓ : ∀ u v r s, WordRel u.val r.val → WordRel v.val s.val → Γ u v=Γ r s) :
    Γ.PosSemidef ↔ (Γ.submatrix chooseWord chooseWord).PosSemidef := by
  constructor
  · exact fun h => h.submatrix chooseWord
  · intro h
    have heq : (Γ.submatrix chooseWord chooseWord).submatrix reduceWord reduceWord=Γ := by
      apply Matrix.ext
      intro u v
      exact hΓ _ _ _ _ (chooseWord_rel u) (chooseWord_rel v)
    have hh := h.submatrix reduceWord
    rwa [heq] at hh

end QuantumBehaviors.NPA
