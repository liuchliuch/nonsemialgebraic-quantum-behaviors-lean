import QuantumBehaviors.Definitions
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Sigma

/-! The syntactic projection-word relations used by the standard binary NPA hierarchy. -/
namespace QuantumBehaviors.NPA

abbrev Letter := Input ⊕ Input
abbrev Word := List Letter

/-- Only the algebraic relations of binary projections and cross-party commutation are generated. -/
inductive WordRel : Word → Word → Prop
  | refl (w) : WordRel w w
  | symm {u v} : WordRel u v → WordRel v u
  | trans {u v w} : WordRel u v → WordRel v w → WordRel u w
  | append {u v x y} : WordRel u v → WordRel x y → WordRel (u++x) (v++y)
  | idem (c : Letter) : WordRel [c,c] [c]
  | cross (i j : Input) : WordRel [Sum.inl i,Sum.inr j] [Sum.inr j,Sum.inl i]

lemma WordRel.reverse {u v : Word} (h : WordRel u v) : WordRel u.reverse v.reverse := by
  induction h with
  | refl w => exact .refl _
  | symm h ih => exact .symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂
  | append h₁ h₂ ih₁ ih₂ => simpa only [List.reverse_append] using WordRel.append ih₂ ih₁
  | idem c => simpa using WordRel.idem c
  | cross i j => simpa using (WordRel.cross i j).symm

lemma WordRel.left_idem (c : Letter) (w : Word) : WordRel (c::c::w) (c::w) := by
  simpa using WordRel.append (WordRel.idem c) (WordRel.refl w)

lemma WordRel.left_cross (i j : Input) (w : Word) :
    WordRel (Sum.inl i::Sum.inr j::w) (Sum.inr j::Sum.inl i::w) := by
  simpa using WordRel.append (WordRel.cross i j) (WordRel.refl w)

lemma WordRel.projection_inner (c : Letter) (u v : Word) :
    WordRel ((c::u).reverse++(c::v)) ((c::u).reverse++v) := by
  simpa [List.reverse_cons,List.append_assoc] using
    WordRel.append (WordRel.refl u.reverse) (WordRel.append (WordRel.idem c) (WordRel.refl v))

variable {A : Type*} [Monoid A]
def wordEval (T : Letter → A) : Word → A
  | [] => 1
  | c::w => T c*wordEval T w

@[simp] lemma wordEval_nil (T : Letter → A) : wordEval T []=1 := rfl
@[simp] lemma wordEval_cons (T : Letter → A) (c : Letter) (w : Word) : wordEval T (c::w)=T c*wordEval T w := rfl
@[simp] lemma wordEval_append (T : Letter → A) (u v : Word) : wordEval T (u++v)=wordEval T u*wordEval T v := by
  induction u with
  | nil => simp
  | cons c u ih => simp only [List.cons_append,wordEval_cons,ih,mul_assoc]

/-- Syntactic equality is sound in every actual projection representation. -/
theorem WordRel.eval_eq {u v : Word} (h : WordRel u v) (T : Letter → A)
    (hid : ∀ c, T c*T c=T c) (hc : ∀ i j, T (Sum.inl i)*T (Sum.inr j)=T (Sum.inr j)*T (Sum.inl i)) :
    wordEval T u=wordEval T v := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append h₁ h₂ ih₁ ih₂ => rw [wordEval_append,wordEval_append,ih₁,ih₂]
  | idem c => simpa using hid c
  | cross i j => simpa using hc i j

lemma wordEval_reverse {A : Type*} [Monoid A] [StarMul A] (T : Letter → A)
    (hT : ∀ c, star (T c)=T c) (w : Word) : wordEval T w.reverse=star (wordEval T w) := by
  induction w with
  | nil => simp
  | cons c w ih => simp [List.reverse_cons,wordEval_append,ih,hT,star_mul]

/-- Redundant literal words of bounded length; finite, with every standard reduced word represented. -/
def BoundedWord (n : ℕ) := {w : Word // w.length ≤ n}

instance (n : ℕ) : Finite (BoundedWord n) := by
  let f : (Σ k : Fin (n+1), Fin k.val → Letter) → BoundedWord n :=
    fun ⟨k,g⟩ => ⟨List.ofFn g,by simp only [List.length_ofFn];omega⟩
  apply Finite.of_surjective f
  rintro ⟨w,hw⟩
  refine ⟨⟨⟨w.length,by omega⟩,w.get⟩,?_⟩
  apply Subtype.ext
  simpa only [f,List.ofFn_get]

noncomputable instance (n : ℕ) : Fintype (BoundedWord n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : DecidableEq (BoundedWord n) := Classical.decEq _

/-- Level k is the standard positive level k+1, so the identity and all single letters occur. -/
def emptyIndex (k : ℕ) : BoundedWord (k+1) := ⟨[],by simp⟩
def letterIndex (k : ℕ) (c : Letter) : BoundedWord (k+1) := ⟨[c],by simp⟩

end QuantumBehaviors.NPA
