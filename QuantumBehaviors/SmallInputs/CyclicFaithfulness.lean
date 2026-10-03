import QuantumBehaviors.SmallInputs.SynchronousTrace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Faithfulness of synchronized operator families on their genuine closed cyclic space. -/

namespace QuantumBehaviors.SmallInputs

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def cyclicWord (B : ι → H →L[ℂ] H) (w : List ι) : H →L[ℂ] H := (w.map B).prod
noncomputable def cyclicSpanAny (B : ι → H →L[ℂ] H) (ψ : H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun w : List ι => cyclicWord B w ψ)
noncomputable def cyclicSpaceAny (B : ι → H →L[ℂ] H) (ψ : H) : Submodule ℂ H :=
  (cyclicSpanAny B ψ).topologicalClosure

instance cyclicSpaceAny_complete (B : ι → H →L[ℂ] H) (ψ : H) :
    CompleteSpace (cyclicSpaceAny B ψ) :=
  inferInstanceAs (CompleteSpace (cyclicSpanAny B ψ).topologicalClosure)

@[simp] lemma cyclicWord_nil (B : ι → H →L[ℂ] H) : cyclicWord B [] = 1 := rfl
@[simp] lemma cyclicWord_cons (B : ι → H →L[ℂ] H) (i : ι) (w : List ι) :
    cyclicWord B (i :: w) = B i * cyclicWord B w := rfl
@[simp] lemma cyclicWord_append (B : ι → H →L[ℂ] H) (u v : List ι) :
    cyclicWord B (u ++ v) = cyclicWord B u * cyclicWord B v := by simp [cyclicWord]
@[simp] lemma cyclicWord_singleton (B : ι → H →L[ℂ] H) (i : ι) : cyclicWord B [i] = B i := by simp [cyclicWord]

lemma cyclicWord_mem (B : ι → H →L[ℂ] H) (ψ : H) (w : List ι) :
    cyclicWord B w ψ ∈ cyclicSpaceAny B ψ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w,rfl⟩)

lemma state_mem_cyclicAny (B : ι → H →L[ℂ] H) (ψ : H) : ψ ∈ cyclicSpaceAny B ψ := by
  simpa using cyclicWord_mem B ψ []

lemma commute_cyclicWord {A : H →L[ℂ] H} {B : ι → H →L[ℂ] H}
    (h : ∀ i, Commute A (B i)) (w : List ι) : Commute A (cyclicWord B w) := by
  apply Commute.list_prod_right
  intro T hT
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hT
  exact h i

lemma synchronized_preserves_cyclicAny {A : H →L[ℂ] H} {B : ι → H →L[ℂ] H} {ψ : H}
    (hcomm : ∀ i, Commute A (B i)) (i : ι) (hsync : A ψ = B i ψ) :
    ∀ x ∈ cyclicSpaceAny B ψ, A x ∈ cyclicSpaceAny B ψ := by
  have hspan : ∀ x ∈ cyclicSpanAny B ψ, A x ∈ cyclicSpanAny B ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨w ++ [i], ?_⟩
      have hw := congrArg (fun T : H →L[ℂ] H => T ψ) (commute_cyclicWord hcomm w).eq
      simpa only [cyclicWord_append, cyclicWord_singleton, ContinuousLinearMap.mul_apply, hsync] using hw.symm
    | zero => simpa using (cyclicSpanAny B ψ).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using (cyclicSpanAny B ψ).add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using (cyclicSpanAny B ψ).smul_mem c ih
  exact Submodule.topologicalClosure_mem_invtSubmodule (f := A) hspan

lemma generator_preserves_cyclicAny (B : ι → H →L[ℂ] H) (ψ : H) (i : ι) :
    ∀ x ∈ cyclicSpaceAny B ψ, B i x ∈ cyclicSpaceAny B ψ := by
  have hspan : ∀ x ∈ cyclicSpanAny B ψ, B i x ∈ cyclicSpanAny B ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨i :: w, rfl⟩
    | zero => simpa using (cyclicSpanAny B ψ).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using (cyclicSpanAny B ψ).add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using (cyclicSpanAny B ψ).smul_mem c ih
  exact Submodule.topologicalClosure_mem_invtSubmodule (f := B i) hspan

noncomputable def cyclicState (B : ι → H →L[ℂ] H) (ψ : H) : cyclicSpaceAny B ψ :=
  ⟨ψ, state_mem_cyclicAny B ψ⟩

noncomputable def cyclicGenerator (B : ι → H →L[ℂ] H) (ψ : H) (i : ι) :
    cyclicSpaceAny B ψ →L[ℂ] cyclicSpaceAny B ψ :=
  QuantumBehaviors.restrictOperator _ (B i) (generator_preserves_cyclicAny B ψ i)

noncomputable def cyclicWordVector (B : ι → H →L[ℂ] H) (ψ : H) (w : List ι) : cyclicSpaceAny B ψ :=
  ⟨cyclicWord B w ψ, cyclicWord_mem B ψ w⟩

@[simp] lemma cyclicWordVector_nil (B : ι → H →L[ℂ] H) (ψ : H) :
    cyclicWordVector B ψ [] = cyclicState B ψ := rfl

@[simp] lemma cyclicWordVector_cons (B : ι → H →L[ℂ] H) (ψ : H) (i : ι) (w : List ι) :
    cyclicWordVector B ψ (i :: w) = cyclicGenerator B ψ i (cyclicWordVector B ψ w) := rfl

/-- A commutant operator vanishing on the cyclic vector vanishes identically.
This is the faithfulness step missing if one applies a faithful-trace variation
argument directly to an arbitrary, possibly nonfaithful vector state. -/
theorem cyclic_commutant_faithful (B : ι → H →L[ℂ] H) (ψ : H)
    (X : cyclicSpaceAny B ψ →L[ℂ] cyclicSpaceAny B ψ)
    (hcomm : ∀ i, Commute X (cyclicGenerator B ψ i)) (hzero : X (cyclicState B ψ) = 0) : X = 0 := by
  let K := cyclicSpaceAny B ψ
  have hword : ∀ w : List ι, X (cyclicWordVector B ψ w) = 0 := by
    intro w
    induction w with
    | nil => exact hzero
    | cons i w ih =>
      rw [cyclicWordVector_cons]
      have he := congrArg (fun T : K →L[ℂ] K => T (cyclicWordVector B ψ w)) (hcomm i).eq
      change X (cyclicGenerator B ψ i (cyclicWordVector B ψ w)) =
        cyclicGenerator B ψ i (X (cyclicWordVector B ψ w)) at he
      rw [ih, map_zero] at he
      exact he
  let F : H →L[ℂ] K := X.comp K.orthogonalProjection
  have hF : Set.EqOn F (0 : H →L[ℂ] K) (Set.range fun w : List ι => cyclicWord B w ψ) := by
    rintro x ⟨w, rfl⟩
    have hp : K.orthogonalProjection (cyclicWord B w ψ) = cyclicWordVector B ψ w := by
      apply Subtype.ext
      exact K.starProjection_eq_self_iff.mpr (cyclicWord_mem B ψ w)
    change X (K.orthogonalProjection (cyclicWord B w ψ)) = 0
    rw [hp]
    exact hword w
  have hall := ContinuousLinearMap.eqOn_closure_span hF
  apply ContinuousLinearMap.ext
  intro x
  have hp : K.orthogonalProjection (x : H) = x := by
    apply Subtype.ext
    exact K.starProjection_eq_self_iff.mpr x.property
  have he := hall x.property
  change X (K.orthogonalProjection (x : H)) = 0 at he
  rw [hp] at he
  exact he

end QuantumBehaviors.SmallInputs
