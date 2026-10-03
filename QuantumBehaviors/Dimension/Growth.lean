import QuantumBehaviors.Dimension.SharedUpper
import QuantumBehaviors.AnalyticScope
import Mathlib.Analysis.Asymptotics.Theta

/-! Corollary S14: exact minimal quantum dimensions, with and without free shared randomness. -/
namespace QuantumBehaviors.Dimension
open Filter Asymptotics
attribute [local instance] Classical.propDecidable

lemma dimension_exists {m : ℕ} (hm : 3 ≤ m) : ∃ d, BoundedFiniteBehavior d d (curve (alpha m)) := by
  obtain ⟨s,hs⟩ := curve_exact_dimension_strategy hm
  exact ⟨24*m,24*m,24*m,le_rfl,le_rfl,s,hs⟩

lemma shared_dimension_exists {m : ℕ} (hm : 3 ≤ m) : ∃ d, SharedBoundedBehavior d d (curve (alpha m)) :=
  ⟨m,curve_shared_upper_bound hm⟩

theorem dimension_bounds {m : ℕ} (hm : 3 ≤ m) : m / Nat.gcd m 2 ≤ D m ∧ D m ≤ 24*m := by
  have hex := dimension_exists hm
  simp only [D,minimumDimension,dif_pos hex]
  constructor
  · obtain ⟨a,b,ha,hb,s,hs⟩ := Nat.find_spec hex
    exact (curve_finite_strategy_dimension_bound hm s hs).1.trans ha
  · apply Nat.find_min'
    obtain ⟨s,hs⟩ := curve_exact_dimension_strategy hm
    exact ⟨24*m,24*m,le_rfl,le_rfl,s,hs⟩

theorem shared_dimension_bounds {m : ℕ} (hm : 3 ≤ m) : m / Nat.gcd m 2 ≤ Dsr m ∧ Dsr m ≤ m := by
  have hex := shared_dimension_exists hm
  simp only [Dsr,minimumSharedDimension,dif_pos hex]
  exact ⟨(curve_shared_dimension_bound hm (Nat.find_spec hex)).1,Nat.find_min' hex (curve_shared_upper_bound hm)⟩

theorem shared_dimension_le_dimension {m : ℕ} (hm : 3 ≤ m) : Dsr m ≤ D m := by
  have hex := dimension_exists hm
  have hexsr := shared_dimension_exists hm
  simp only [Dsr,minimumSharedDimension,dif_pos hexsr,D,minimumDimension,dif_pos hex]
  exact Nat.find_min' hexsr (bounded_implies_shared (Nat.find_spec hex))

lemma denominator_linear_bounds {m : ℕ} (hm : 0 < m) :
    m ≤ 2 * (m / Nat.gcd m 2) ∧ m / Nat.gcd m 2 ≤ m := by
  have hg : Nat.gcd m 2 ≤ 2 := Nat.gcd_le_right m (by omega)
  have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left m 2)
  constructor
  · nlinarith
  · exact Nat.div_le_self _ _

lemma reciprocal_gap {m : ℕ} (hm : 0 < m) : (2 - alpha m)⁻¹ = (m : ℝ) / 2 := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  dsimp [alpha]
  field_simp
  ring

lemma growth_of_linear_bounds (f : ℕ → ℕ) (C : ℕ)
    (hb : ∀ m, 3 ≤ m → m / Nat.gcd m 2 ≤ f m ∧ f m ≤ C*m) :
    (fun m => (f m : ℝ)) =Θ[atTop] (fun m => (2 - alpha m)⁻¹) := by
  constructor
  · apply IsBigO.of_bound (2*C : ℝ)
    filter_upwards [eventually_ge_atTop 3] with m hm
    rw [reciprocal_gap (by omega)]
    have h := (hb m hm).2
    have hR : (f m : ℝ) ≤ (C : ℝ) * m := by exact_mod_cast h
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ f m by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ)/2 by positivity)]
    nlinarith
  · apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 3] with m hm
    rw [reciprocal_gap (by omega)]
    have hl := (denominator_linear_bounds (m := m) (by omega)).1
    have hf := (hb m hm).1
    have hN : m ≤ 2*f m := by omega
    have hR : (m : ℝ) ≤ 2*(f m : ℝ) := by exact_mod_cast hN
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ f m by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ)/2 by positivity)]
    linarith

theorem dimension_growth : (fun m => (D m : ℝ)) =Θ[atTop] (fun m => (2-alpha m)⁻¹) :=
  growth_of_linear_bounds D 24 (fun m hm => dimension_bounds hm)

theorem shared_dimension_growth : (fun m => (Dsr m : ℝ)) =Θ[atTop] (fun m => (2-alpha m)⁻¹) := by
  apply growth_of_linear_bounds Dsr 1
  intro m hm
  simpa using shared_dimension_bounds hm

/-- All dimension statements of S14, including the classical limiting behavior. -/
theorem corollary_S14 :
    (∀ m, 3 ≤ m → m / Nat.gcd m 2 ≤ Dsr m ∧ Dsr m ≤ m ∧
      m / Nat.gcd m 2 ≤ D m ∧ D m ≤ 24*m) ∧
    (fun m => (D m : ℝ)) =Θ[atTop] (fun m => (2-alpha m)⁻¹) ∧
    (fun m => (Dsr m : ℝ)) =Θ[atTop] (fun m => (2-alpha m)⁻¹) ∧
    Tendsto (fun m => curve (alpha m)) atTop (nhds (curve 2)) ∧ BellLocal (curve 2) := by
  refine ⟨?_,dimension_growth,shared_dimension_growth,?_,curve_two_local⟩
  · intro m hm
    exact ⟨(shared_dimension_bounds hm).1,(shared_dimension_bounds hm).2,dimension_bounds hm⟩
  · exact curve_alpha_tendsto_classical

end QuantumBehaviors.Dimension
