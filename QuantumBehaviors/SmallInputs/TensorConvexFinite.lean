import QuantumBehaviors.SmallInputs.TensorConvexBinary
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Finite convexification has an explicit linear dimension budget, including zero-weight branches. -/
namespace QuantumBehaviors.SmallInputs
open Finset Set
open scoped BigOperators
variable {nA nB mA mB D E : ℕ}

lemma boundedDimension_mono (hDE : D ≤ E) : Scenarios.BoundedDimensionSet nA nB mA mB D ⊆
    Scenarios.BoundedDimensionSet nA nB mA mB E := by
  rintro p ⟨a,b,ha,hb,hp⟩
  exact ⟨a,b,ha.trans hDE,hb.trans hDE,hp⟩

theorem centerMass_bounded {J : Type*} (t : Finset J) (w : J → ℝ)
    (z : J → Scenarios.Behavior nA nB mA mB)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i ∈ t, w i)
    (hz : ∀ i ∈ t, z i ∈ Scenarios.BoundedDimensionSet nA nB mA mB D) :
    t.centerMass w z ∈ Scenarios.BoundedDimensionSet nA nB mA mB (t.card*D) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hpos
  | @insert i t hi ih =>
    have zi := hz i (mem_insert_self i t)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => hw j (mem_insert_of_mem hj)
    have hmem : ∀ j ∈ t, z j ∈ Scenarios.BoundedDimensionSet nA nB mA mB D := fun j hj => hz j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hpos
    by_cases hsum : ∑ j ∈ t, w j=0
    · have hzero : ∀ j ∈ t, w j=0 := (sum_eq_zero_iff_of_nonneg hs₀).mp hsum
      have hwz : ∑ j ∈ t, w j • z j=0 := sum_eq_zero fun j hj => by simp [hzero j hj]
      simp only [Finset.centerMass,sum_insert hi,hsum,hwz,add_zero]
      have hwi : w i ≠ 0 := by linarith
      rw [← mul_smul,inv_mul_cancel₀ hwi,one_smul]
      exact boundedDimension_mono (by rw [card_insert_of_notMem hi]; nlinarith) zi
    · have htpos : 0 < ∑ j ∈ t, w j := lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum)
      have ht := ih hs₀ htpos hmem
      rw [Finset.centerMass_insert _ _ _ hi hsum]
      have hpair := convex_pair_bounded zi ht
        (div_nonneg (hw i (mem_insert_self i t)) hpos.le) (div_nonneg htpos.le hpos.le)
        (by rw [← add_div,div_self (ne_of_gt hpos)])
      simpa only [card_insert_of_notMem hi,Nat.add_mul,one_mul,Nat.add_comm D] using hpair

/-- Carathéodory's affine-independent support gives a dimension budget of (ambient dimension+1)D. -/
theorem convexHull_bounded_dimension : convexHull ℝ (Scenarios.BoundedDimensionSet nA nB mA mB D) ⊆
    Scenarios.BoundedDimensionSet nA nB mA mB ((Module.finrank ℝ (Scenarios.Behavior nA nB mA mB)+1)*D) := by
  classical
  intro p hp
  let t := Caratheodory.minCardFinsetOfMemConvexHull hp
  have hsub : (t : Set (Scenarios.Behavior nA nB mA mB)) ⊆ Scenarios.BoundedDimensionSet nA nB mA mB D :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hp
  have hAI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hp
  have hcard : t.card ≤ Module.finrank ℝ (Scenarios.Behavior nA nB mA mB)+1 := by
    have h := hAI.card_le_finrank_succ
    have hle := (vectorSpan ℝ (Set.range ((↑) : t → Scenarios.Behavior nA nB mA mB))).finrank_le
    have hcard' : t.card ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Scenarios.Behavior nA nB mA mB)))+1 := by
      simpa only [Fintype.card_coe] using h
    exact hcard'.trans (Nat.add_le_add_right hle 1)
  have ht : p ∈ convexHull ℝ (t : Set (Scenarios.Behavior nA nB mA mB)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hp
  rw [Finset.convexHull_eq] at ht
  obtain ⟨w,hw,hws,hp⟩ := ht
  have hb := centerMass_bounded t w id hw (by rw [hws];norm_num) (fun i hi => hsub hi)
  rw [hp] at hb
  exact boundedDimension_mono (Nat.mul_le_mul_right D hcard) hb

theorem three_convexHull_bounded444 : convexHull ℝ (Scenarios.BoundedDimensionSet 3 3 2 2 12) ⊆
    Scenarios.BoundedDimensionSet 3 3 2 2 444 := by
  simpa [Scenarios.Behavior,Scenarios.Coordinate] using
    (convexHull_bounded_dimension (nA := 3) (nB := 3) (mA := 2) (mB := 2) (D := 12))

end QuantumBehaviors.SmallInputs
