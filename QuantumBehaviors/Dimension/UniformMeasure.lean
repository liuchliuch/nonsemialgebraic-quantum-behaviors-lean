import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace QuantumBehaviors.Dimension
open MeasureTheory
open scoped BigOperators ENNReal
variable (J : Type*) [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]

noncomputable def uniformMeasure : Measure J := (Fintype.card J : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure (uniformMeasure J) where
  measure_univ := by
    simp only [uniformMeasure, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := J)) (by simp)

lemma integral_uniformMeasure (f : J → ℝ) :
    (∫ j, f j ∂uniformMeasure J) = (Fintype.card J : ℝ)⁻¹ * ∑ j, f j := by
  rw [uniformMeasure, integral_smul_measure, integral_count]
  simp

end QuantumBehaviors.Dimension
