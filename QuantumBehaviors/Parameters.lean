import QuantumBehaviors.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

/-! The exact allowed sequence and explicit forbidden points in every left tail at 2. -/
namespace QuantumBehaviors

open Filter Set
open scoped Topology

theorem alpha_mem_Ioo {m : ℕ} (hm : 3 ≤ m) : alpha m ∈ Ioo (1 : ℝ) 2 := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  constructor
  · dsimp [alpha]
    have : 2 / (m : ℝ) < 1 := (div_lt_one hmpos).mpr (by linarith)
    linarith
  · dsimp [alpha]
    have : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hmpos
    linarith

theorem alpha_strictMonoOn : StrictMonoOn alpha (Ici 1) := by
  intro m hm n hn hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  unfold alpha
  have : 2 / (n : ℝ) < 2 / (m : ℝ) := by
    apply (div_lt_div_iff₀ hnR hmR).mpr
    nlinarith
  linarith

theorem alpha_spacing {m : ℕ} (hm : 0 < m) :
    alpha (m + 1) - alpha m = 2 / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hm)
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [alpha, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem exists_alpha_above {β : ℝ} (hβ : β < 2) :
    ∃ m : ℕ, 3 ≤ m ∧ β < alpha m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (3 : ℝ) (2 / (2 - β)))
  have hm3 : (3 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmb : 2 / (2 - β) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hden : 0 < 2 - β := by linarith
  have hproduct : 2 < (m : ℝ) * (2 - β) := (div_lt_iff₀ hden).mp hmb
  refine ⟨m, ?_, ?_⟩
  · have : 3 < m := by exact_mod_cast hm3
    omega
  · unfold alpha
    have : 2 / (m : ℝ) < 2 - β := (div_lt_iff₀ hmpos).mpr (by nlinarith)
    linarith

/-- A rational parameter strictly between two consecutive allowed parameters. -/
noncomputable def forbidden (m : ℕ) : ℝ := 2 - 4 / (2 * (m : ℝ) + 1)

theorem alpha_lt_forbidden {m : ℕ} (hm : 0 < m) : alpha m < forbidden m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hden : (0 : ℝ) < 2 * m + 1 := by positivity
  have hdiv : 4 / (2 * (m : ℝ) + 1) < 2 / (m : ℝ) := by
    apply (div_lt_div_iff₀ hden hmR).mpr
    nlinarith
  dsimp [alpha, forbidden]
  linarith

theorem forbidden_lt_two (m : ℕ) : forbidden m < 2 := by
  have hden : (0 : ℝ) < 2 * m + 1 := by positivity
  have : 0 < 4 / (2 * (m : ℝ) + 1) := div_pos (by norm_num) hden
  dsimp [forbidden]
  linarith

theorem forbidden_not_allowed (m : ℕ) : ¬ Allowed (forbidden m) := by
  rintro ⟨k, hk, heq⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hden : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hfrac : 4 / (2 * (m : ℝ) + 1) = 2 / (k : ℝ) := by
    dsimp [forbidden, alpha] at heq
    linarith
  have hmul : (2 : ℝ) * k = 2 * m + 1 := by
    field_simp at hfrac
    nlinarith
  have hnat : 2 * k = 2 * m + 1 := by exact_mod_cast hmul
  omega

theorem allowed_and_forbidden_in_tail {β : ℝ} (hβ : β < 2) :
    (∃ α ∈ Ioo (max 1 β) 2, Allowed α) ∧
    (∃ α ∈ Ioo (max 1 β) 2, ¬ Allowed α) := by
  have hmax : max (1 : ℝ) β < 2 := max_lt (by norm_num) hβ
  obtain ⟨m, hm, hma⟩ := exists_alpha_above hmax
  constructor
  · exact ⟨alpha m, ⟨hma, (alpha_mem_Ioo hm).2⟩, m, hm, rfl⟩
  · refine ⟨forbidden m, ⟨?_, forbidden_lt_two m⟩, forbidden_not_allowed m⟩
    exact lt_trans hma (alpha_lt_forbidden (by omega))

end QuantumBehaviors
