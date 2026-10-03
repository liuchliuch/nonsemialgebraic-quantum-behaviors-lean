import QuantumBehaviors.Dimension.FiniteLower
import QuantumBehaviors.QuantumMoments

namespace QuantumBehaviors
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem FiniteStrategy.probability_nonnegative {dA dB : ℕ} (s : FiniteStrategy dA dB)
    {p : Behavior} (hp : s.realizes p) : Nonnegative p := by
  rintro ⟨i,j,a,b⟩
  have hA : (effect (s.alice i) a).PosSemidef := by cases a; exact s.alice_complement_pos i; exact s.alice_pos i
  have hB : (effect (s.bob j) b).PosSemidef := by cases b; exact s.bob_complement_pos j; exact s.bob_pos j
  have h := (densityFunctional s.density s.density_pos).map_nonneg (hA.kronecker hB).nonneg
  change 0 ≤ (s.density * (effect (s.alice i) a ⊗ₖ effect (s.bob j) b)).trace at h
  rw [← hp] at h
  exact (RCLike.nonneg_iff.mp h).1

theorem cqc_witness_nonnegative {p : Behavior} (hp : p ∈ Cqc) (hs : Synchronous p) (α : ℝ) :
    0 ≤ witness p α := by
  obtain ⟨H, hN, hI, hC, s, hreal⟩ := hp
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  have hn : 0 ≤ (inner ℂ ((∑ i, s.alice i) s.state - (α : ℂ) • s.state)
    ((∑ i, s.alice i) s.state - (α : ℂ) • s.state)).re := inner_self_nonneg (𝕜 := ℂ) (x := ((∑ i, s.alice i) s.state - (α : ℂ) • s.state))
  rw [commuting_witness_inner s hreal hs α] at hn
  exact hn

theorem cq_witness_nonnegative {p : Behavior} (hp : p ∈ Cq) (hs : Synchronous p) (α : ℝ) :
    0 ≤ witness p α := cqc_witness_nonnegative (cq_subset_cqc hp) hs α

end QuantumBehaviors
