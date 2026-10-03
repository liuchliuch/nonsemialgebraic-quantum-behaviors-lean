import QuantumBehaviors.NPA.Models
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Infinite Gram vectors and syntactic relations reconstruct a genuine commuting model. -/
namespace QuantumBehaviors.NPA
open Matrix
open scoped BigOperators

noncomputable def vectorBorn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : Word → H) (i j : Input) (a b : Bool) : ℂ :=
  let α := inner ℂ (v []) (v [Sum.inl i])
  let β := inner ℂ (v []) (v [Sum.inr j])
  let γ := inner ℂ (v [Sum.inl i]) (v [Sum.inr j])
  if a then if b then γ else α-γ else if b then β-γ else 1-α-β+γ

structure GramRepresentation (p : Behavior) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  vector : Word → H
  normalized : inner ℂ (vector []) (vector [])=1
  relations : ∀ u v r s, WordRel (u.reverse++v) (r.reverse++s) → inner ℂ (vector u) (vector v)=inner ℂ (vector r) (vector s)
  born : ∀ i j a b, (p (i,j,a,b) : ℂ)=vectorBorn vector i j a b

variable {p : Behavior} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (g : GramRepresentation p H)

noncomputable def GramRepresentation.space : Submodule ℂ H := (Submodule.span ℂ (Set.range g.vector)).topologicalClosure
noncomputable instance : CompleteSpace g.space := inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range g.vector)).topologicalClosure)

noncomputable def GramRepresentation.word (w : Word) : g.space :=
  ⟨g.vector w,Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w,rfl⟩)⟩

@[simp] lemma GramRepresentation.word_inner (u v : Word) : inner ℂ (g.word u) (g.word v)=inner ℂ (g.vector u) (g.vector v) := rfl

lemma GramRepresentation.word_eq_of_rel {u v : Word} (h : WordRel u v) : g.word u=g.word v := by
  have h1 := g.relations u u u v (WordRel.append (WordRel.refl u.reverse) h)
  have h2 := g.relations v u v v (WordRel.append (WordRel.refl v.reverse) h)
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change inner ℂ (g.vector u-g.vector v) (g.vector u-g.vector v)=0
  rw [inner_sub_left,inner_sub_right,inner_sub_right,h1,h2]
  ring

noncomputable def GramRepresentation.letterSpace (c : Letter) : Submodule ℂ g.space :=
  (Submodule.span ℂ (Set.range fun w : Word => g.word (c::w))).topologicalClosure
noncomputable instance (c : Letter) : CompleteSpace (g.letterSpace c) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (Set.range fun w : Word => g.word (c::w))).topologicalClosure)

noncomputable def GramRepresentation.operator (c : Letter) : g.space →L[ℂ] g.space :=
  (g.letterSpace c).starProjection

lemma GramRepresentation.operator_projection (c : Letter) : IsStarProjection (g.operator c) :=
  isStarProjection_starProjection

lemma GramRepresentation.operator_word (c : Letter) (w : Word) : g.operator c (g.word w)=g.word (c::w) := by
  have hy : g.word (c::w) ∈ g.letterSpace c := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w,rfl⟩)
  let F : g.space →L[ℂ] ℂ := innerSL ℂ (g.word w-g.word (c::w))
  have hspan : Submodule.span ℂ (Set.range fun u : Word => g.word (c::u)) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨u,rfl⟩
    change inner ℂ (g.word w-g.word (c::w)) (g.word (c::u))=0
    rw [inner_eq_zero_symm,inner_sub_right,g.word_inner,g.word_inner]
    exact sub_eq_zero.mpr (g.relations (c::u) w (c::u) (c::w) (WordRel.projection_inner c u w).symm)
  have hclosed : g.letterSpace c ≤ F.ker := Submodule.topologicalClosure_minimal _ hspan F.isClosed_ker
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy (fun z hz => hclosed hz)

/-- The constructed word vectors are total in their explicitly closed cyclic Hilbert space. -/
lemma GramRepresentation.ext_on_words {S T : g.space →L[ℂ] g.space}
    (h : ∀ w, S (g.word w)=T (g.word w)) : S=T := by
  let F : H →L[ℂ] g.space := (S-T).comp g.space.orthogonalProjection
  have hspan : Submodule.span ℂ (Set.range g.vector) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨w,rfl⟩
    have he : g.space.orthogonalProjection (g.vector w)=g.word w :=
      g.space.orthogonalProjection_mem_subspace_eq_self (g.word w)
    change (S-T) (g.space.orthogonalProjection (g.vector w))=0
    rw [he,ContinuousLinearMap.sub_apply,h,sub_self]
  have hk : g.space ≤ F.ker := Submodule.topologicalClosure_minimal _ hspan F.isClosed_ker
  apply ContinuousLinearMap.ext
  intro x
  have hx := hk x.property
  change (S-T) (g.space.orthogonalProjection (x : H))=0 at hx
  rw [g.space.orthogonalProjection_mem_subspace_eq_self,ContinuousLinearMap.sub_apply] at hx
  exact sub_eq_zero.mp hx

lemma GramRepresentation.cross_commute (i j : Input) : Commute (g.operator (Sum.inl i)) (g.operator (Sum.inr j)) := by
  change g.operator (Sum.inl i)*g.operator (Sum.inr j)=g.operator (Sum.inr j)*g.operator (Sum.inl i)
  apply g.ext_on_words
  intro w
  simp only [ContinuousLinearMap.mul_apply,g.operator_word]
  exact g.word_eq_of_rel (WordRel.left_cross i j w)

noncomputable def GramRepresentation.strategy : CommutingStrategy g.space where
  state := g.word []
  state_norm := by
    have h : inner ℂ (g.word []) (g.word [])=1 := g.normalized
    rw [inner_self_eq_norm_sq_to_K] at h
    have hs : ‖g.word []‖^2=(1 : ℝ) := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_pow,Complex.ofReal_one] using h
    nlinarith [norm_nonneg (g.word [])]
  alice := fun i => g.operator (Sum.inl i)
  bob := fun j => g.operator (Sum.inr j)
  alice_projection := fun i => g.operator_projection _
  bob_projection := fun j => g.operator_projection _
  cross_commute := g.cross_commute

lemma GramRepresentation.strategy_realizes : g.strategy.realizes p := by
  intro i j a b
  rw [g.born]
  have hjoint : inner ℂ (g.vector []) (g.vector [Sum.inl i,Sum.inr j])=
      inner ℂ (g.vector [Sum.inl i]) (g.vector [Sum.inr j]) :=
    g.relations _ _ _ _ (WordRel.refl _)
  change vectorBorn g.vector i j a b=inner ℂ (g.word [])
    ((effect (g.operator (Sum.inl i)) a*effect (g.operator (Sum.inr j)) b) (g.word []))
  cases a <;> cases b <;>
    simp only [vectorBorn,effect_false,effect_true,ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_sub,g.operator_word,
      inner_sub_right,g.word_inner,g.normalized,hjoint,Bool.false_eq_true,↓reduceIte]
  all_goals ring

include g in
theorem GramRepresentation.mem_cqc : p ∈ Cqc :=
  ⟨g.space,inferInstance,inferInstance,inferInstance,g.strategy,g.strategy_realizes⟩

end QuantumBehaviors.NPA
