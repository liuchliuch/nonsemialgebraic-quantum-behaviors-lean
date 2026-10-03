import QuantumBehaviors.SmallInputs.SynchronousTrace
import QuantumBehaviors.Scenarios.ClosedCommuting
import Mathlib.Topology.Order.Compact

/-! Compactness of the genuine synchronous commuting sector in every finite scenario. -/

namespace QuantumBehaviors.SmallInputs

variable {nA nB mA mB : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commuting_probability_square (s : Scenarios.CommutingStrategy nA nB mA mB H)
    {p : Scenarios.Behavior nA nB mA mB} (hr : s.realizes p)
    (i : Fin nA) (j : Fin nB) (a : Fin mA) (b : Fin mB) :
    p (i,j,a,b) = ‖(s.alice i a * s.bob j b) s.state‖ ^ 2 := by
  have hP := (s.alice_projection i a).mul (s.bob_projection j b) (s.cross_commute i j a b)
  have he : (p (i,j,a,b) : ℂ) =
      inner ℂ ((s.alice i a * s.bob j b) s.state) ((s.alice i a * s.bob j b) s.state) := by
    rw [projection_inner_self _ hP]
    exact hr i j a b
  have hre := congrArg Complex.re he
  change p (i,j,a,b) = RCLike.re (inner ℂ _ _) at hre
  rwa [inner_self_eq_norm_sq] at hre

lemma commuting_probability_bounds (s : Scenarios.CommutingStrategy nA nB mA mB H)
    {p : Scenarios.Behavior nA nB mA mB} (hr : s.realizes p)
    (i : Fin nA) (j : Fin nB) (a : Fin mA) (b : Fin mB) :
    0 ≤ p (i,j,a,b) ∧ p (i,j,a,b) ≤ 1 := by
  rw [commuting_probability_square s hr i j a b]
  have hP := (s.alice_projection i a).mul (s.bob_projection j b) (s.cross_commute i j a b)
  have hn := (s.alice i a * s.bob j b).le_opNorm s.state
  rw [s.state_norm, mul_one] at hn
  have h1 : ‖(s.alice i a * s.bob j b) s.state‖ ≤ 1 := hn.trans hP.norm_le
  exact ⟨sq_nonneg _, by nlinarith [norm_nonneg ((s.alice i a * s.bob j b) s.state)]⟩

lemma cqc_subset_unit_cube : Scenarios.Cqc nA nB mA mB ⊆
    Set.Icc (fun _ => 0) (fun _ => 1) := by
  rintro p ⟨H,hN,hI,hC,s,hr⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  constructor <;> rintro ⟨i,j,a,b⟩
  · exact (commuting_probability_bounds s hr i j a b).1
  · exact (commuting_probability_bounds s hr i j a b).2

/-- A closed subset of the finite probability cube is compact. -/
theorem cqc_compact (nA nB mA mB : ℕ) : IsCompact (Scenarios.Cqc nA nB mA mB) :=
  IsCompact.of_isClosed_subset isCompact_Icc (Scenarios.cqc_isClosed nA nB mA mB)
    cqc_subset_unit_cube

lemma synchronous_isClosed (n : ℕ) : IsClosed {p : Scenarios.Behavior n n 2 2 | Scenarios.Synchronous p} := by
  have he : {p : Scenarios.Behavior n n 2 2 | Scenarios.Synchronous p} =
      ⋂ i : Fin n, ⋂ a : Fin 2, ⋂ b : Fin 2, ⋂ (_ : a ≠ b),
        {p | p (i,i,a,b) = 0} := by ext p; simp [Scenarios.Synchronous]
  rw [he]
  refine isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun (_ : a ≠ b) => ?_
  exact isClosed_eq (continuous_apply (i,i,a,b)) continuous_const

/-- No finite-dimensional realization theorem is used in this compactness result. -/
theorem synchronous_cqc_compact (n : ℕ) : IsCompact (Scenarios.synchronousSet n .qc) :=
  (cqc_compact n n 2 2).inter_right (synchronous_isClosed n)

end QuantumBehaviors.SmallInputs
