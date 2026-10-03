import QuantumBehaviors.Basic
import QuantumBehaviors.Parameters
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Sign.Basic

/-!
# Genuine finite sign descriptions

Semialgebraic descriptions here are finite Boolean combinations of signs of multivariate
polynomials with arbitrary real coefficients. The definition does not build in closure under
projection. Semianalytic descriptions require functions analytic on an open neighborhood
containing the point in question.
-/

namespace QuantumBehaviors

open Filter Set
open scoped Topology

/-- An analytic real function has constant sign on a sufficiently short left-hand interval. -/
theorem analytic_eventually_left_sign {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ s : SignType, ∀ᶠ x in 𝓝[<] x₀, SignType.sign (f x) = s := by
  classical
  by_cases hzero : ∀ᶠ x in 𝓝 x₀, f x = 0
  · refine ⟨0, ?_⟩
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds] with x hx
    simp [hx]
  · obtain ⟨n, g, hg, hg0, heq⟩ :=
      hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
    have hsign : ∀ᶠ x in 𝓝 x₀, SignType.sign (g x) = SignType.sign (g x₀) := by
      exact ((continuousAt_sign_of_ne_zero hg0).comp hg.continuousAt).tendsto.eventually
        (isOpen_discrete _ |>.mem_nhds (by simp : SignType.sign (g x₀) ∈ {SignType.sign (g x₀)}))
    refine ⟨(-1 : SignType) ^ n * SignType.sign (g x₀), ?_⟩
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
      hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hsg hxlt
    rw [hx]
    change SignType.sign ((x - x₀) ^ n * g x) = _
    rw [sign_mul, sign_pow, sign_neg (sub_neg.mpr hxlt), hsg]

/-- Finite Boolean truth values stabilize together with their finite collection of signs. -/
theorem analytic_formula_eventually_left {n : ℕ} (f : Fin n → ℝ → ℝ)
    (φ : SignFormula (Fin n)) {x₀ : ℝ} (hf : ∀ i, AnalyticAt ℝ (f i) x₀) :
    ∃ b : Bool, ∀ᶠ x in 𝓝[<] x₀,
      φ.eval (fun i => SignType.sign (f i x)) = b := by
  classical
  choose s hs using fun i => analytic_eventually_left_sign (hf i)
  refine ⟨φ.eval s, ?_⟩
  have hall : ∀ᶠ x in 𝓝[<] x₀, ∀ i, SignType.sign (f i x) = s i :=
    (Filter.eventually_all).mpr hs
  filter_upwards [hall] with x hx
  congr 1
  exact funext hx

theorem curve_coordinate_analytic (c : Coordinate) (α : ℝ) :
    AnalyticAt ℝ (fun x => curve x c) α := by
  rcases c with ⟨i, j, a, b⟩
  cases a <;> cases b <;> by_cases h : i = j <;> simp [curve, h]
  all_goals fun_prop

theorem curve_analytic (α : ℝ) : AnalyticAt ℝ curve α :=
  AnalyticAt.pi fun c => curve_coordinate_analytic c α

theorem curve_continuous : Continuous curve :=
  continuous_iff_continuousAt.mpr fun α => (curve_analytic α).continuousAt

theorem polynomial_curve_analytic (p : MvPolynomial Coordinate ℝ) (α : ℝ) :
    AnalyticAt ℝ (fun x => MvPolynomial.eval (curve x) p) α := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using (analyticAt_const (v := r) (x := α))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p c hp =>
      simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (curve_coordinate_analytic c α)

theorem semialgebraic_curve_eventually_left {C : Set Behavior} (hC : IsSemialgebraic C) :
    ∃ b : Bool, ∀ᶠ α in 𝓝[<] (2 : ℝ), (curve α ∈ C ↔ b = true) := by
  obtain ⟨n, f, φ, hφ⟩ := hC
  obtain ⟨b, hb⟩ := analytic_formula_eventually_left
    (fun i α => MvPolynomial.eval (curve α) (f i)) φ
    (fun i => polynomial_curve_analytic (f i) 2)
  refine ⟨b, ?_⟩
  filter_upwards [hb] with α hα
  rw [hφ, hα]

theorem semianalytic_curve_eventually_left {C : Set Behavior}
    (hC : IsSemianalyticAt C (curve 2)) :
    ∃ b : Bool, ∀ᶠ α in 𝓝[<] (2 : ℝ), (curve α ∈ C ↔ b = true) := by
  obtain ⟨U, n, f, φ, hU, h2, hf, hφ⟩ := hC
  have hmem : ∀ᶠ α in 𝓝 (2 : ℝ), curve α ∈ U :=
    (curve_continuous.continuousAt).tendsto.eventually (hU.mem_nhds h2)
  obtain ⟨b, hb⟩ := analytic_formula_eventually_left
    (fun i α => f i (curve α)) φ
    (fun i => (hf i _ h2).comp (curve_analytic 2))
  refine ⟨b, ?_⟩
  filter_upwards [hb, hmem.filter_mono nhdsWithin_le_nhds] with α hα hαU
  rw [hφ (curve α) hαU, hα]

/-- An exact allowed slice cannot have eventually constant left membership. -/
theorem exact_slice_not_eventually_constant {C : Set Behavior}
    (hslice : ∀ α ∈ Ioo (1 : ℝ) 2, curve α ∈ C ↔ Allowed α) :
    ¬ ∃ b : Bool, ∀ᶠ α in 𝓝[<] (2 : ℝ), (curve α ∈ C ↔ b = true) := by
  rintro ⟨b, hb⟩
  obtain ⟨β, hβ, htail⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hb
  obtain ⟨⟨a, ha, haAllowed⟩, ⟨c, hc, hcForbidden⟩⟩ := allowed_and_forbidden_in_tail hβ
  have ha1 : 1 < a := lt_of_le_of_lt (le_max_left _ _) ha.1
  have hab : β < a := lt_of_le_of_lt (le_max_right _ _) ha.1
  have hc1 : 1 < c := lt_of_le_of_lt (le_max_left _ _) hc.1
  have hcb : β < c := lt_of_le_of_lt (le_max_right _ _) hc.1
  have hbtrue : b = true := (htail ⟨hab, ha.2⟩).mp ((hslice a ⟨ha1, ha.2⟩).mpr haAllowed)
  exact hcForbidden ((hslice c ⟨hc1, hc.2⟩).mp ((htail ⟨hcb, hc.2⟩).mpr hbtrue))

/-- Geometric part of Corollary S8, with the exact slice provided separately. -/
theorem exact_slice_not_semialgebraic {C : Set Behavior}
    (hslice : ∀ α ∈ Ioo (1 : ℝ) 2, curve α ∈ C ↔ Allowed α) :
    ¬ IsSemialgebraic C := fun h =>
  exact_slice_not_eventually_constant hslice (semialgebraic_curve_eventually_left h)

/-- Geometric part of Proposition S9; analyticity is required at the endpoint itself. -/
theorem exact_slice_not_semianalytic {C : Set Behavior}
    (hslice : ∀ α ∈ Ioo (1 : ℝ) 2, curve α ∈ C ↔ Allowed α) :
    ¬ IsSemianalyticAt C (curve 2) := fun h =>
  exact_slice_not_eventually_constant hslice (semianalytic_curve_eventually_left h)

/-- Proposition S12 for any semialgebraic set containing every constructed quantum point. -/
theorem semialgebraic_tail {R : Set Behavior} (hR : IsSemialgebraic R)
    (hall : ∀ m : ℕ, 3 ≤ m → curve (alpha m) ∈ R) :
    ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, curve α ∈ R := by
  obtain ⟨b, hb⟩ := semialgebraic_curve_eventually_left hR
  obtain ⟨β, hβ, htail⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hb
  obtain ⟨m, hm, hma⟩ := exists_alpha_above hβ
  have hbtrue : b = true := (htail ⟨hma, (alpha_mem_Ioo hm).2⟩).mp (hall m hm)
  let γ := (max 1 β + 2) / 2
  have hm2 : max (1 : ℝ) β < 2 := max_lt (by norm_num) hβ
  have hγ : max (1 : ℝ) β < γ ∧ γ < 2 := by dsimp [γ]; constructor <;> linarith
  refine ⟨γ, ⟨lt_of_le_of_lt (le_max_left _ _) hγ.1, hγ.2⟩, ?_⟩
  intro α hα
  exact (htail ⟨lt_trans (lt_of_le_of_lt (le_max_right _ _) hγ.1) hα.1, hα.2⟩).mpr hbtrue

end QuantumBehaviors
