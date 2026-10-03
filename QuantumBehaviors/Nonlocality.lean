import QuantumBehaviors.Classical
import Mathlib.Tactic.Push

/-! Full behavior nonlocality from synchrony and the integer-valued zero-variance witness. -/
namespace QuantumBehaviors

open scoped BigOperators

noncomputable def witnessLinear (α : ℝ) : Behavior →ₗ[ℝ] ℝ where
  toFun p := (∑ i : Input, ∑ j : Input, p (i, j, true, true)) -
    2 * α * (∑ i : Input, p (i, i, true, true))
  map_add' p q := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem witness_eq_linear (p : Behavior) (α : ℝ) : witness p α = witnessLinear α p + α ^ 2 := rfl

theorem witness_mixture {n : ℕ} (w : Fin n → ℝ) (r : Fin n → Behavior)
    (hw : (∑ k, w k) = 1) (α : ℝ) :
    witness (∑ k, w k • r k) α = ∑ k, w k * witness (r k) α := by
  simp only [witness_eq_linear, map_sum, map_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hw, one_mul]

theorem deterministic_nonnegative (A B : Response) (x : Coordinate) :
    0 ≤ deterministic A B x := by
  rcases x with ⟨i, j, a, b⟩
  dsimp only [deterministic]
  split_ifs <;> norm_num

theorem synchronous_mismatch {p : Behavior} (hp : Synchronous p)
    (i : Input) {a b : Bool} (hab : a ≠ b) : p (i, i, a, b) = 0 := by
  cases a <;> cases b
  · exact False.elim (hab rfl)
  · exact (hp i).2
  · exact (hp i).1
  · exact False.elim (hab rfl)

theorem positive_local_branch_synchronous {p : Behavior} {n : ℕ}
    (w : Fin n → ℝ) (A B : Fin n → Response) (hw : ∀ k, 0 ≤ w k)
    (hreal : ∀ x, p x = ∑ k, w k * deterministic (A k) (B k) x)
    (hp : Synchronous p) {k : Fin n} (hk : 0 < w k) : A k = B k := by
  funext i
  by_contra hab
  have hzero := synchronous_mismatch hp i hab
  have hle := Finset.single_le_sum
    (fun l (hl : l ∈ (Finset.univ : Finset (Fin n))) =>
      mul_nonneg (hw l) (deterministic_nonnegative (A l) (B l) (i, i, A k i, B k i)))
    (Finset.mem_univ k)
  rw [← hreal, hzero] at hle
  simp only [deterministic, and_self, ↓reduceIte, mul_one] at hle
  exact (not_le_of_gt hk) hle

/-- Proposition S13, first part: no point of the curve with 1<α<2 is Bell local. -/
theorem curve_not_bellLocal {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) : ¬ BellLocal (curve α) := by
  rintro ⟨n, w, A, B, hw, hsum, hreal⟩
  have hbranch : ∀ k, 0 < w k → A k = B k :=
    fun k hk => positive_local_branch_synchronous w A B hw hreal (curve_synchronous α) hk
  have hp : curve α = ∑ k, w k • deterministic (A k) (A k) := by
    funext x
    rw [hreal]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hzero : w k = 0
    · simp [hzero]
    · rw [hbranch k (lt_of_le_of_ne (hw k) (Ne.symm hzero))]
  have hF : (∑ k, w k * ((deterministicCount (A k) : ℝ) - α) ^ 2) = 0 := by
    have h := curve_witness α
    rw [hp, witness_mixture w _ hsum] at h
    simpa only [deterministic_witness] using h
  obtain ⟨k, hk⟩ : ∃ k, 0 < w k := by
    by_contra h
    push_neg at h
    have hle : (∑ k, w k) ≤ 0 := Finset.sum_nonpos fun k hk => h k
    linarith
  have hle := Finset.single_le_sum
    (fun l (hl : l ∈ (Finset.univ : Finset (Fin n))) => mul_nonneg (hw l) (sq_nonneg ((deterministicCount (A l) : ℝ) - α)))
    (Finset.mem_univ k)
  rw [hF] at hle
  have hz : ((deterministicCount (A k) : ℝ) - α) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((deterministicCount (A k) : ℝ) - α)]
  have heq : (deterministicCount (A k) : ℝ) = α := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hlow : 1 < deterministicCount (A k) := by exact_mod_cast (heq.symm ▸ hα₁)
  have hhigh : deterministicCount (A k) < 2 := by exact_mod_cast (heq.symm ▸ hα₂)
  omega

end QuantumBehaviors
