import QuantumBehaviors.Dimension.SharedLower

/-! Measurable physical probability kernels automatically meet the integrability condition. -/
namespace QuantumBehaviors
open Matrix MeasureTheory
open scoped BigOperators Kronecker ComplexOrder

theorem FiniteStrategy.probability_normalized {dA dB : ℕ} (s : FiniteStrategy dA dB)
    {p : Behavior} (hp : s.realizes p) : Normalized p := by
  intro i j
  have htensor : (∑ a : Bool, ∑ b : Bool, effect (s.alice i) a ⊗ₖ effect (s.bob j) b) =
      (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) := by
    ext ⟨r,u⟩ ⟨v,w⟩
    by_cases hr : r=v <;> by_cases hu : u=w <;>
      simp [Matrix.sum_apply,effect,Matrix.one_apply,Prod.mk.injEq,hr,hu] <;> ring
  have h : ((∑ a : Bool, ∑ b : Bool, p (i,j,a,b) : ℝ) : ℂ) = 1 := by
    calc
      _ = ∑ a : Bool, ∑ b : Bool, (s.density * (effect (s.alice i) a ⊗ₖ effect (s.bob j) b)).trace := by
        simp only [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hp i j a b
      _ = (s.density * (∑ a : Bool, ∑ b : Bool, effect (s.alice i) a ⊗ₖ effect (s.bob j) b)).trace := by
        simp only [Matrix.mul_sum,Matrix.trace_sum]
      _ = 1 := by rw [htensor,mul_one,s.density_trace]

  exact_mod_cast h

theorem FiniteStrategy.probability_le_one {dA dB : ℕ} (s : FiniteStrategy dA dB)
    {p : Behavior} (hp : s.realizes p) (x : Coordinate) : p x ≤ 1 := by
  rcases x with ⟨i,j,a,b⟩
  have hn := s.probability_nonnegative hp
  have hsum := s.probability_normalized hp i j
  rw [← hsum]
  calc
    p (i,j,a,b) ≤ ∑ b : Bool, p (i,j,a,b) := Finset.single_le_sum (fun k (hk : k ∈ (Finset.univ : Finset Bool)) => hn (i,j,a,k)) (Finset.mem_univ b)
    _ ≤ ∑ a : Bool, ∑ b : Bool, p (i,j,a,b) :=
      Finset.single_le_sum (fun k (hk : k ∈ (Finset.univ : Finset Bool)) =>
        Finset.sum_nonneg (fun l (hl : l ∈ (Finset.univ : Finset Bool)) => hn (i,j,k,l))) (Finset.mem_univ a)

namespace Dimension

theorem SharedRandomnessRealizes.of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {r : Ω → Behavior} {p : Behavior} {dA dB : ℕ}
    (hmeas : ∀ x, AEMeasurable (fun ω => r ω x) μ)
    (hb : ∀ x, (∫ ω, r ω x ∂μ) = p x)
    (hr : ∀ᵐ ω ∂μ, BoundedFiniteBehavior dA dB (r ω)) :
    SharedRandomnessRealizes μ r p dA dB := by
  refine ⟨?_,hb,hr⟩
  intro x
  apply Integrable.of_mem_Icc 0 1 (hmeas x)
  filter_upwards [hr] with ω hω
  obtain ⟨a,b,ha,hb,s,hs⟩ := hω
  exact ⟨s.probability_nonnegative hs x,s.probability_le_one hs x⟩

end Dimension
end QuantumBehaviors
