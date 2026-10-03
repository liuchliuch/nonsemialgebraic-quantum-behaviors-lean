import QuantumBehaviors.Dimension.Definitions
import QuantumBehaviors.Dimension.BehaviorFacts
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Arbitrary probability-space shared randomness and its almost-sure rank constraint. -/
namespace QuantumBehaviors.Dimension
open MeasureTheory Filter
open scoped BigOperators ENNReal

lemma integrable_witness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : Ω → Behavior) (hi : ∀ x, Integrable (fun ω => r ω x) μ) (α : ℝ) :
    Integrable (fun ω => witness (r ω) α) μ := by
  apply Integrable.add
  · apply Integrable.sub
    · exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi (i,j,true,true)
    · exact (integrable_finset_sum _ fun i _ => hi (i,i,true,true)).const_mul _
  · exact integrable_const _

lemma integral_witness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Behavior) (p : Behavior) (hi : ∀ x, Integrable (fun ω => r ω x) μ)
    (hb : ∀ x, (∫ ω, r ω x ∂μ) = p x) (α : ℝ) :
    (∫ ω, witness (r ω) α ∂μ) = witness p α := by
  have hfirst := integrable_finset_sum (s := Finset.univ) fun i _ => hi (i,i,true,true)
  have hsecond := integrable_finset_sum (s := Finset.univ) fun i _ =>
    integrable_finset_sum (s := Finset.univ) fun j _ => hi (i,j,true,true)
  simp only [witness]
  have hadd := integral_add (hsecond.sub (hfirst.const_mul (2*α))) (integrable_const (α^2))
  have hsub := integral_sub hsecond (hfirst.const_mul (2*α))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hi (i,j,true,true)),
    integral_finset_sum _ (fun i _ => hi (i,i,true,true))]
  simp_rw [integral_finset_sum _ (fun j _ => hi (_,j,true,true)), hb]
  simp

theorem SharedRandomnessRealizes.synchronous_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {r : Ω → Behavior} {p : Behavior} {dA dB : ℕ}
    (h : SharedRandomnessRealizes μ r p dA dB) (hs : Synchronous p) :
    ∀ᵐ ω ∂μ, Synchronous (r ω) := by
  have hnn : ∀ᵐ ω ∂μ, Nonnegative (r ω) := h.branches.mono fun ω hω => by
    obtain ⟨a,b,ha,hb,s,hr⟩ := hω
    exact s.probability_nonnegative hr
  have hz (i : Input) (a b : Bool) (hp : p (i,i,a,b) = 0) :
      ∀ᵐ ω ∂μ, r ω (i,i,a,b) = 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae (hnn.mono fun ω hω => hω _) (h.coordinate_integrable _)).mp
    rw [h.barycenter, hp]
  have h10 : ∀ᵐ ω ∂μ, ∀ i : Input, r ω (i,i,true,false) = 0 :=
    ae_all_iff.mpr fun i => hz i true false (hs i).1
  have h01 : ∀ᵐ ω ∂μ, ∀ i : Input, r ω (i,i,false,true) = 0 :=
    ae_all_iff.mpr fun i => hz i false true (hs i).2
  filter_upwards [h10,h01] with ω h10 h01
  exact fun i => ⟨h10 i,h01 i⟩

theorem SharedRandomnessRealizes.zero_witness_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {r : Ω → Behavior} {p : Behavior} {dA dB : ℕ}
    (h : SharedRandomnessRealizes μ r p dA dB) (hs : Synchronous p) {α : ℝ}
    (hF : witness p α = 0) : ∀ᵐ ω ∂μ, Synchronous (r ω) ∧ witness (r ω) α = 0 := by
  have hsync := h.synchronous_ae hs
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ witness (r ω) α := by
    filter_upwards [hsync,h.branches] with ω hs hr
    obtain ⟨a,b,ha,hb,s,hreal⟩ := hr
    exact cq_witness_nonnegative ⟨a,b,s,hreal⟩ hs α
  have hz : ∀ᵐ ω ∂μ, witness (r ω) α = 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_witness μ r h.coordinate_integrable α)).mp
    rw [integral_witness μ r p h.coordinate_integrable h.barycenter, hF]
  exact hsync.and hz

theorem SharedRandomnessRealizes.dimension_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {r : Ω → Behavior} {p : Behavior} {dA dB m : ℕ}
    (h : SharedRandomnessRealizes μ r p dA dB) (hm : 3 ≤ m) (hs : Synchronous p)
    (hF : witness p (alpha m) = 0) : m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB := by
  have hh := (h.zero_witness_ae hs hF).and h.branches
  obtain ⟨ω,hω⟩ := hh.exists
  obtain ⟨a,b,ha,hb,s,hreal⟩ := hω.2
  have hd := finite_strategy_dimension_bound hm s (r ω) hreal hω.1.1 hω.1.2
  exact ⟨hd.1.trans ha,hd.2.trans hb⟩

theorem curve_shared_dimension_bound {dA dB m : ℕ} (hm : 3 ≤ m)
    (h : SharedBoundedBehavior dA dB (curve (alpha m))) :
    m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB := by
  obtain ⟨Ω,hM,μ,hμ,r,hr⟩ := h
  letI : MeasurableSpace Ω := hM
  letI : IsProbabilityMeasure μ := hμ
  exact hr.dimension_bound hm (curve_synchronous _) (curve_witness _)

end QuantumBehaviors.Dimension
