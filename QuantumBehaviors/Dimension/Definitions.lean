import QuantumBehaviors.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The dimension costs in S14, including arbitrary shared classical randomness. -/
namespace QuantumBehaviors.Dimension
open MeasureTheory Filter
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

/-- Each conditional strategy has both prescribed local dimension bounds. -/
def BoundedFiniteBehavior (dA dB : ℕ) (p : Behavior) : Prop :=
  ∃ a b : ℕ, a ≤ dA ∧ b ≤ dB ∧ ∃ s : FiniteStrategy a b, s.realizes p

/-- A measurable probabilistic mixture, written coordinatewise in its finite behavior space.
Coordinate integrability is the usual barycenter condition; no finite-support restriction is made. -/
structure SharedRandomnessRealizes {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → Behavior) (p : Behavior) (dA dB : ℕ) : Prop where
  coordinate_integrable : ∀ x, Integrable (fun ω => r ω x) μ
  barycenter : ∀ x, (∫ ω, r ω x ∂μ) = p x
  branches : ∀ᵐ ω ∂μ, BoundedFiniteBehavior dA dB (r ω)

/-- Shared randomness ranges over arbitrary probability spaces and arbitrary integrable mixtures. -/
def SharedBoundedBehavior (dA dB : ℕ) (p : Behavior) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (r : Ω → Behavior), SharedRandomnessRealizes μ r p dA dB

noncomputable def minimumDimension (p : Behavior) : ℕ :=
  if h : ∃ D, BoundedFiniteBehavior D D p then Nat.find h else 0

noncomputable def minimumSharedDimension (p : Behavior) : ℕ :=
  if h : ∃ D, SharedBoundedBehavior D D p then Nat.find h else 0

noncomputable def D (m : ℕ) : ℕ := minimumDimension (curve (alpha m))
noncomputable def Dsr (m : ℕ) : ℕ := minimumSharedDimension (curve (alpha m))

end QuantumBehaviors.Dimension
