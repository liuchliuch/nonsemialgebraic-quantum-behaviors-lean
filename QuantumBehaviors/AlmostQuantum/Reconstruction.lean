import QuantumBehaviors.AlmostQuantum.Models
import QuantumBehaviors.ComplexSemidefinite
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Every finite event certificate constructs actual almost-quantum Hilbert projections. -/
namespace QuantumBehaviors.AlmostQuantum
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def gramVector (Γ : Matrix Event Event ℂ) (e : Event) : EuclideanSpace ℂ Event :=
  WithLp.toLp 2 (fun k => CFC.sqrt Γ k e)

lemma gramVector_inner {Γ : Matrix Event Event ℂ} (hΓ : Γ.PosSemidef) (e f : Event) :
    inner ℂ (gramVector Γ e) (gramVector Γ f)=Γ e f := by
  have hs : (CFC.sqrt Γ).conjTranspose=CFC.sqrt Γ := (CFC.sqrt_nonneg Γ).isSelfAdjoint
  have hsq : (CFC.sqrt Γ).conjTranspose*CFC.sqrt Γ=Γ := by rw [hs,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg]
  have he : inner ℂ (gramVector Γ e) (gramVector Γ f)=((CFC.sqrt Γ).conjTranspose*CFC.sqrt Γ) e f := by
    simp [gramVector,PiLp.inner_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm]
  rw [he,hsq]

section Projection
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

noncomputable def spanProjection (v : J → E) : E →L[ℂ] E :=
  (Submodule.span ℂ (Set.range v)).starProjection

lemma spanProjection_projection (v : J → E) : IsStarProjection (spanProjection v) :=
  isStarProjection_starProjection

lemma spanProjection_apply (v : J → E) {x y : E} (hy : ∃ j, v j=y)
    (hinner : ∀ j, inner ℂ (v j) x=inner ℂ (v j) y) : spanProjection v x=y := by
  let K := Submodule.span ℂ (Set.range v)
  have hym : y ∈ K := Submodule.subset_span hy
  apply Submodule.eq_starProjection_of_mem_orthogonal hym
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j,rfl⟩ := hz
      rw [inner_sub_right,hinner,sub_self]
  | zero => simp
  | add u v hu hv ihu ihv => rw [inner_add_left,ihu,ihv,add_zero]
  | smul c z hz ih => rw [inner_smul_left,ih,mul_zero]
end Projection

variable {p : Behavior} (c : Certificate p)

noncomputable def Certificate.aliceOperator (i : Input) : EuclideanSpace ℂ Event →L[ℂ] EuclideanSpace ℂ Event :=
  spanProjection (fun t => gramVector c.gram (aliceRow i t))
noncomputable def Certificate.bobOperator (j : Input) : EuclideanSpace ℂ Event →L[ℂ] EuclideanSpace ℂ Event :=
  spanProjection (fun t => gramVector c.gram (bobRow j t))

lemma Certificate.alice_empty_action (i : Input) :
    c.aliceOperator i (gramVector c.gram emptyEvent)=gramVector c.gram (aliceEvent i) := by
  apply spanProjection_apply _ ⟨none,rfl⟩
  intro t
  rw [gramVector_inner c.positive,gramVector_inner c.positive,c.alice_empty]
  rfl

lemma Certificate.alice_bob_action (i j : Input) :
    c.aliceOperator i (gramVector c.gram (bobEvent j))=gramVector c.gram (jointEvent i j) := by
  apply spanProjection_apply _ ⟨some j,rfl⟩
  intro t
  rw [gramVector_inner c.positive,gramVector_inner c.positive,c.alice_bob]
  rfl

lemma Certificate.bob_empty_action (j : Input) :
    c.bobOperator j (gramVector c.gram emptyEvent)=gramVector c.gram (bobEvent j) := by
  apply spanProjection_apply _ ⟨none,rfl⟩
  intro t
  rw [gramVector_inner c.positive,gramVector_inner c.positive,c.bob_empty]
  rfl

lemma Certificate.bob_alice_action (i j : Input) :
    c.bobOperator j (gramVector c.gram (aliceEvent i))=gramVector c.gram (jointEvent i j) := by
  apply spanProjection_apply _ ⟨some i,rfl⟩
  intro t
  rw [gramVector_inner c.positive,gramVector_inner c.positive,c.bob_alice]
  rfl

noncomputable def Certificate.strategy : Strategy (EuclideanSpace ℂ Event) where
  state := gramVector c.gram emptyEvent
  state_norm := by
    have h := gramVector_inner c.positive emptyEvent emptyEvent
    rw [c.normalized,inner_self_eq_norm_sq_to_K] at h
    have hs : ‖gramVector c.gram emptyEvent‖^2=(1 : ℝ) := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_pow,Complex.ofReal_one] using h
    nlinarith [norm_nonneg (gramVector c.gram emptyEvent)]
  alice := c.aliceOperator
  bob := c.bobOperator
  alice_projection := fun i => spanProjection_projection _
  bob_projection := fun j => spanProjection_projection _
  cross_on_state := by
    intro i j
    rw [c.bob_empty_action,c.alice_empty_action,c.alice_bob_action,c.bob_alice_action]

lemma Certificate.strategy_realizes : c.strategy.realizes p := by
  intro i j a b
  rw [c.born]
  change bornValue c.gram i j a b=inner ℂ (gramVector c.gram emptyEvent)
    ((effect (c.aliceOperator i) a*effect (c.bobOperator j) b) (gramVector c.gram emptyEvent))
  cases a <;> cases b <;>
    simp only [bornValue,effect_false,effect_true,ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_sub,inner_sub_right,
      c.alice_empty_action,c.bob_empty_action,c.alice_bob_action,gramVector_inner c.positive,c.normalized,
      Bool.false_eq_true,↓reduceIte]
  all_goals ring

/-- Genuine operator realizations are equivalent to the explicit 25-event finite Gram SDP. -/
theorem mem_iff_certificate (p : Behavior) : p ∈ behaviors ↔ Nonempty (Certificate p) := by
  constructor
  · rintro ⟨H,hN,hI,hC,s,hs⟩
    letI : NormedAddCommGroup H := hN
    letI : InnerProductSpace ℂ H := hI
    letI : CompleteSpace H := hC
    exact ⟨s.certificate hs⟩
  · rintro ⟨c⟩
    exact ⟨EuclideanSpace ℂ Event,inferInstance,inferInstance,inferInstance,c.strategy,c.strategy_realizes⟩

end QuantumBehaviors.AlmostQuantum
