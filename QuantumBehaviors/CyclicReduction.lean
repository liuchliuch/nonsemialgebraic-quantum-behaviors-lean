import QuantumBehaviors.Models
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Promoting synchronized vector relations to a scalar operator identity

The closed cyclic subspace includes the empty Bob word. This is the infinite-dimensional
operator step in Lemma S6; no faithful state or finite dimension is required.
-/

namespace QuantumBehaviors

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def bobWord (B : Input → H →L[ℂ] H) (w : List Input) : H →L[ℂ] H :=
  (w.map B).prod

@[simp] theorem bobWord_nil (B : Input → H →L[ℂ] H) : bobWord B [] = 1 := rfl

@[simp] theorem bobWord_append (B : Input → H →L[ℂ] H) (u v : List Input) :
    bobWord B (u ++ v) = bobWord B u * bobWord B v := by simp [bobWord]

@[simp] theorem bobWord_singleton (B : Input → H →L[ℂ] H) (i : Input) :
    bobWord B [i] = B i := by simp [bobWord]

noncomputable def cyclicSpan (B : Input → H →L[ℂ] H) (ψ : H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun w : List Input => bobWord B w ψ)

noncomputable def cyclicSpace (B : Input → H →L[ℂ] H) (ψ : H) : Submodule ℂ H :=
  (cyclicSpan B ψ).topologicalClosure

theorem state_mem_cyclicSpan (B : Input → H →L[ℂ] H) (ψ : H) : ψ ∈ cyclicSpan B ψ := by
  apply Submodule.subset_span
  exact ⟨[], by simp⟩

theorem state_mem_cyclicSpace (B : Input → H →L[ℂ] H) (ψ : H) : ψ ∈ cyclicSpace B ψ :=
  Submodule.le_topologicalClosure _ (state_mem_cyclicSpan B ψ)

theorem cyclicSpace_nontrivial (B : Input → H →L[ℂ] H) {ψ : H} (hψ : ψ ≠ 0) :
    Nontrivial (cyclicSpace B ψ) := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro h
  have := state_mem_cyclicSpace B ψ
  rw [h] at this
  exact hψ this

theorem commute_bobWord {A : H →L[ℂ] H} {B : Input → H →L[ℂ] H}
    (h : ∀ j, Commute A (B j)) (w : List Input) : Commute A (bobWord B w) := by
  apply Commute.list_prod_right
  intro X hX
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hX
  exact h j

theorem alice_preserves_cyclicSpan {A : H →L[ℂ] H} {B : Input → H →L[ℂ] H}
    {ψ : H} (hcomm : ∀ j, Commute A (B j)) (i : Input) (hsync : A ψ = B i ψ) :
    ∀ x ∈ cyclicSpan B ψ, A x ∈ cyclicSpan B ψ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨w ++ [i], ?_⟩
      have hw := congrArg (fun T : H →L[ℂ] H => T ψ) (commute_bobWord hcomm w).eq
      simpa only [bobWord_append, bobWord_singleton, ContinuousLinearMap.mul_apply, hsync] using hw.symm
  | zero => simpa using (cyclicSpan B ψ).zero_mem
  | add x y hx hy hAx hAy => simpa only [map_add] using (cyclicSpan B ψ).add_mem hAx hAy
  | smul c x hx hAx => simpa only [map_smul] using (cyclicSpan B ψ).smul_mem c hAx

theorem alice_preserves_cyclicSpace {A : H →L[ℂ] H} {B : Input → H →L[ℂ] H}
    {ψ : H} (hcomm : ∀ j, Commute A (B j)) (i : Input) (hsync : A ψ = B i ψ) :
    ∀ x ∈ cyclicSpace B ψ, A x ∈ cyclicSpace B ψ := by
  have hspan := alice_preserves_cyclicSpan hcomm i hsync
  have hInv : cyclicSpan B ψ ∈ Module.End.invtSubmodule A.toLinearMap := hspan
  exact Submodule.topologicalClosure_mem_invtSubmodule (f := A) hInv

noncomputable def restrictOperator (K : Submodule ℂ H) (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) : K →L[ℂ] K :=
  (A.comp K.subtypeL).codRestrict K fun x => hA x x.property

@[simp] theorem restrictOperator_apply (K : Submodule ℂ H) (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) (x : K) :
    ((restrictOperator K A hA x : K) : H) = A x := rfl

theorem restrictOperator_projection (K : Submodule ℂ H) [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ K, A x ∈ K) (hp : IsStarProjection A) :
    IsStarProjection (restrictOperator K A hA) := by
  constructor
  · ext x
    change A (A x) = A x
    exact congrArg (fun T : H →L[ℂ] H => T x) hp.isIdempotentElem.eq
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    exact hp.isSelfAdjoint.isSymmetric x y

/-- The scalar relation propagates from the unit vector to its closed cyclic subspace. -/
theorem scalar_on_cyclicSpace {S : H →L[ℂ] H} {B : Input → H →L[ℂ] H} {ψ : H}
    {α : ℝ} (hcomm : ∀ j, Commute S (B j)) (hscalar : S ψ = (α : ℂ) • ψ) :
    ∀ x ∈ cyclicSpace B ψ, S x = (α : ℂ) • x := by
  let T : H →L[ℂ] H := (α : ℂ) • 1
  have hgen : Set.EqOn S T (Set.range fun w : List Input => bobWord B w ψ) := by
    rintro x ⟨w, rfl⟩
    have hw := congrArg (fun A : H →L[ℂ] H => A ψ) (commute_bobWord hcomm w).eq
    simpa only [ContinuousLinearMap.mul_apply, hscalar, map_smul,
      T, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using hw
  exact ContinuousLinearMap.eqOn_closure_span hgen

/-- Pure operator-theoretic core of S6. Inputs are the two vector identities obtained from moments. -/
theorem synchronized_scalar_restriction
    (s : CommutingStrategy H) (α : ℝ)
    (hsync : ∀ i, s.alice i s.state = s.bob i s.state)
    (hscalar : (∑ i, s.alice i) s.state = (α : ℂ) • s.state) :
    ∃ (K : Submodule ℂ H) (_ : CompleteSpace K) (_ : Nontrivial K)
      (P : Input → K →L[ℂ] K),
      (∀ i, IsStarProjection (P i)) ∧
      (∑ i, P i) = algebraMap ℝ (K →L[ℂ] K) α := by
  let K := cyclicSpace s.bob s.state
  have hψ : s.state ≠ 0 := by
    intro h
    simpa [h] using s.state_norm
  letI : CompleteSpace K := inferInstanceAs (CompleteSpace (cyclicSpan s.bob s.state).topologicalClosure)
  letI : Nontrivial K := cyclicSpace_nontrivial s.bob hψ
  have hInv : ∀ i x, x ∈ K → s.alice i x ∈ K := fun i =>
    alice_preserves_cyclicSpace (s.cross_commute i) i (hsync i)
  let P : Input → K →L[ℂ] K := fun i => restrictOperator K (s.alice i) (hInv i)
  refine ⟨K, inferInstance, inferInstance, P, ?_, ?_⟩
  · intro i
    exact restrictOperator_projection K (s.alice i) (hInv i) (s.alice_projection i)
  · have hSumComm : ∀ j, Commute (∑ i, s.alice i) (s.bob j) := by
      intro j
      exact Commute.sum_left Finset.univ s.alice (s.bob j) (fun i hi => s.cross_commute i j)
    have hK := scalar_on_cyclicSpace hSumComm hscalar
    ext x
    simpa [P, restrictOperator, ContinuousLinearMap.sum_apply,
      Algebra.algebraMap_eq_smul_one] using hK x x.property

end QuantumBehaviors
