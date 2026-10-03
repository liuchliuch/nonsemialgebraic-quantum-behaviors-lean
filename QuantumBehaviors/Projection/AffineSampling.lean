import QuantumBehaviors.Projection.FiniteFormula
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Complete sign sampling for affine univariate families

For `aᵢ t + bᵢ`, every realized sign vector occurs at minus infinity, at a root,
or immediately to the right of a root. All of these samples are determined by the
finite polynomial list `aᵢ`, `bᵢ`, `aᵢ bⱼ - aⱼ bᵢ`. This file proves the sampling part;
`AffineElimination.lean` compiles those data into an explicit quantifier-free formula.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Set
open scoped Topology

variable {ι : Type*}

/-- The unique zero of a nonconstant affine function; only used when `a ≠ 0`. -/
def affineRoot (a b : ℝ) : ℝ := -b / a

lemma affine_eq_mul_sub_root {a b : ℝ} (ha : a ≠ 0) (t : ℝ) :
    a * t + b = a * (t - affineRoot a b) := by
  dsimp [affineRoot]
  field_simp
  <;> ring

lemma affine_eval_root {a b : ℝ} (ha : a ≠ 0) : a * affineRoot a b + b = 0 := by
  rw [affine_eq_mul_sub_root ha]
  simp

lemma affine_eq_zero_iff {a b t : ℝ} (ha : a ≠ 0) :
    a * t + b = 0 ↔ t = affineRoot a b := by
  rw [affine_eq_mul_sub_root ha, mul_eq_zero]
  simp [ha, sub_eq_zero]

/-- Sign at the left unbounded interval. -/
def affineBotSign (a b : ℝ) : SignType :=
  if a = 0 then SignType.sign b else -SignType.sign a

/-- Sign immediately to the right of a given sample location. -/
def affineRightSign (a b r : ℝ) : SignType :=
  if a * r + b = 0 then SignType.sign a else SignType.sign (a * r + b)

lemma affine_sign_of_lt_root {a b t : ℝ} (ha : a ≠ 0) (ht : t < affineRoot a b) :
    SignType.sign (a * t + b) = affineBotSign a b := by
  rw [affine_eq_mul_sub_root ha, sign_mul, sign_neg (sub_neg.mpr ht)]
  simp [affineBotSign, ha]

lemma affine_sign_of_root_lt {a b t : ℝ} (ha : a ≠ 0) (ht : affineRoot a b < t) :
    SignType.sign (a * t + b) = SignType.sign a := by
  rw [affine_eq_mul_sub_root ha, sign_mul, sign_pos (sub_pos.mpr ht), mul_one]

lemma affine_eventually_bot (a b : ℝ) :
    ∀ᶠ t in atBot, SignType.sign (a * t + b) = affineBotSign a b := by
  by_cases ha : a = 0
  · simp [ha, affineBotSign]
  · filter_upwards [eventually_lt_atBot (affineRoot a b)] with t ht
    exact affine_sign_of_lt_root ha ht

lemma affine_eventually_right (a b r : ℝ) :
    ∀ᶠ t in 𝓝[>] r, SignType.sign (a * t + b) = affineRightSign a b r := by
  by_cases hz : a * r + b = 0
  · have heq (t : ℝ) : a * t + b = a * (t - r) := by linarith
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [heq, sign_mul, sign_pos (sub_pos.mpr ht), mul_one]
    simp [affineRightSign, hz]
  · have hc : ContinuousAt (fun t : ℝ => a * t + b) r := by fun_prop
    have hs : ∀ᶠ t in 𝓝 r, SignType.sign (a * t + b) = SignType.sign (a * r + b) := by
      exact ((continuousAt_sign_of_ne_zero hz).comp (f := fun t : ℝ => a * t + b) hc).tendsto.eventually
        (isOpen_discrete _ |>.mem_nhds (by simp : SignType.sign (a * r + b) ∈
          {SignType.sign (a * r + b)}))
    simpa [affineRightSign, hz] using hs.filter_mono nhdsWithin_le_nhds

/-- A right-germ sign vector of finitely many affine functions is realized by a real point. -/
theorem affine_right_sign_realized [Fintype ι] (a b : ι → ℝ) (r : ℝ) :
    ∃ t : ℝ, ∀ i, SignType.sign (a i * t + b i) = affineRightSign (a i) (b i) r := by
  have h : ∀ᶠ t in 𝓝[>] r, ∀ i,
      SignType.sign (a i * t + b i) = affineRightSign (a i) (b i) r :=
    Filter.eventually_all.mpr fun i => affine_eventually_right (a i) (b i) r
  exact h.exists

/-- The left-infinity sign vector of finitely many affine functions is realized. -/
theorem affine_bot_sign_realized [Fintype ι] (a b : ι → ℝ) :
    ∃ t : ℝ, ∀ i, SignType.sign (a i * t + b i) = affineBotSign (a i) (b i) := by
  have h : ∀ᶠ t in atBot, ∀ i,
      SignType.sign (a i * t + b i) = affineBotSign (a i) (b i) :=
    Filter.eventually_all.mpr fun i => affine_eventually_bot (a i) (b i)
  exact h.exists

/-- There are no additional affine sign patterns between successive roots. -/
lemma affine_sign_of_no_root_between {a b r t : ℝ} (hrt : r < t)
    (hgap : a ≠ 0 → affineRoot a b ≤ t → affineRoot a b ≤ r) :
    SignType.sign (a * t + b) = affineRightSign a b r := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0 <;> simp [affineRightSign, hb]
  by_cases hz : a * r + b = 0
  · have hr := (affine_eq_zero_iff ha).mp hz
    rw [affineRightSign, if_pos hz]
    exact affine_sign_of_root_lt ha (hr ▸ hrt)
  by_cases hroot : affineRoot a b ≤ r
  · have hstrict : affineRoot a b < r := lt_of_le_of_ne hroot (fun heq =>
      hz ((affine_eq_zero_iff ha).mpr heq.symm))
    rw [affineRightSign, if_neg hz, affine_sign_of_root_lt ha hstrict,
      affine_sign_of_root_lt ha (lt_trans hstrict hrt)]
  · have htroot : t < affineRoot a b := lt_of_not_ge (fun h => hroot (hgap ha h))
    rw [affineRightSign, if_neg hz, affine_sign_of_lt_root ha htroot,
      affine_sign_of_lt_root ha (lt_trans hrt htroot)]

/-- Complete finite sampling theorem for arbitrary affine sign formulas. -/
theorem affine_sign_sampling [Fintype ι] (a b : ι → ℝ) (t : ℝ) :
    (∀ j, SignType.sign (a j * t + b j) = affineBotSign (a j) (b j)) ∨
    ∃ i, a i ≠ 0 ∧
      ((∀ j, SignType.sign (a j * t + b j) =
        SignType.sign (a j * affineRoot (a i) (b i) + b j)) ∨
      (∀ j, SignType.sign (a j * t + b j) =
        affineRightSign (a j) (b j) (affineRoot (a i) (b i)))) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => a i ≠ 0 ∧ affineRoot (a i) (b i) ≤ t
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi, himax⟩ := s.exists_max_image (fun i => affineRoot (a i) (b i)) hs
    have hi' : a i ≠ 0 ∧ affineRoot (a i) (b i) ≤ t := (Finset.mem_filter.mp hi).2
    refine Or.inr ⟨i, hi'.1, ?_⟩
    rcases hi'.2.eq_or_lt with h | h
    · exact Or.inl (by intro j; rw [h])
    · apply Or.inr
      intro j
      apply affine_sign_of_no_root_between h
      intro hj hjt
      exact himax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjt⟩)
  · apply Or.inl
    intro j
    by_cases hj : a j = 0
    · simp [hj, affineBotSign]
    · apply affine_sign_of_lt_root hj
      apply lt_of_not_ge
      intro hroot
      exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hroot⟩⟩

end QuantumBehaviors.Projection
