import QuantumBehaviors.Basic
import Mathlib.Data.Real.Archimedean

/-!
# Arithmetic descent for two reflected spectral sets

This file isolates the discrete, dimension-independent part of the argument.
Its hypotheses are subsequently proved for genuine operator spectra.
-/

namespace QuantumBehaviors

/-- A nonnegative set with fixed-step descent, stopping only at `0` or `δ / 2`,
is contained in the nonnegative half-step lattice. -/
theorem descent_lattice {S : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hdescent : ∀ x ∈ S, x ≠ 0 → x ≠ δ / 2 → x - δ ∈ S) :
    ∀ x ∈ S, ∃ j : ℕ, x = (j : ℝ) * (δ / 2) := by
  have hbounded : ∀ n : ℕ, ∀ x ∈ S, x < (n : ℝ) * δ →
      ∃ j : ℕ, x = (j : ℝ) * (δ / 2) := by
    intro n
    induction n with
    | zero =>
        intro x hx hbound
        have := hnonneg x hx
        simp only [Nat.cast_zero, zero_mul] at hbound
        linarith
    | succ n ih =>
        intro x hx hbound
        by_cases hzero : x = 0
        · exact ⟨0, by simpa using hzero⟩
        by_cases hhalf : x = δ / 2
        · exact ⟨1, by simpa using hhalf⟩
        have hprev := hdescent x hx hzero hhalf
        obtain ⟨j, hj⟩ := ih (x - δ) hprev (by
          push_cast at hbound
          nlinarith)
        refine ⟨j + 2, ?_⟩
        push_cast
        nlinarith
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (x / δ)
  apply hbounded n x hx
  exact (div_lt_iff₀ hδ).mp hn

/-- Two nonempty, positive, complementary reflected spectra force exactly the
integer parameters in the four-projection theorem. -/
theorem allowed_of_reflected_sets {S T : Set ℝ} {α : ℝ}
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (hne : S.Nonempty)
    (hS : ∀ x ∈ S, 0 ≤ x)
    (hT : ∀ x ∈ T, 0 ≤ x)
    (hcomplement : ∀ x : ℝ, α - x ∈ T ↔ x ∈ S)
    (hreflectS : ∀ x ∈ S, 0 < x → x < 2 → 2 - x ∈ S)
    (hreflectT : ∀ x ∈ T, 0 < x → x < 2 → 2 - x ∈ T) :
    Allowed α := by
  let δ : ℝ := 4 - 2 * α
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbound : ∀ x ∈ S, x ≤ α := by
    intro x hx
    have := hT (α - x) ((hcomplement x).mpr hx)
    linarith
  have hdescent : ∀ x ∈ S, x ≠ 0 → x ≠ δ / 2 → x - δ ∈ S := by
    intro x hx hxzero hxhalf
    have hxpos : 0 < x := lt_of_le_of_ne (hS x hx) (Ne.symm hxzero)
    have hxupper : x < 2 := lt_of_le_of_lt (hbound x hx) hα₂
    have hr := hreflectS x hx hxpos hxupper
    have hrbound := hbound (2 - x) hr
    have hrne : 2 - x ≠ α := by
      intro heq
      apply hxhalf
      dsimp [δ]
      linarith
    have hμpos : 0 < α - (2 - x) := by
      have := lt_of_le_of_ne hrbound hrne
      linarith
    have hμupper : α - (2 - x) < 2 := by linarith
    have hμ := (hcomplement (2 - x)).mpr hr
    have hμreflection := hreflectT (α - (2 - x)) hμ hμpos hμupper
    apply (hcomplement (x - δ)).mp
    convert hμreflection using 1 <;> dsimp [δ] <;> ring
  have hlattice := descent_lattice hδ hS hdescent
  have hpositive : ∃ x ∈ S, 0 < x := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxzero : x = 0
    · have hzero : 0 ∈ S := hxzero ▸ hx
      have hαT : α ∈ T := by simpa using (hcomplement 0).mpr hzero
      have hαref := hreflectT α hαT (by linarith) hα₂
      have hnew : 2 * α - 2 ∈ S := by
        apply (hcomplement (2 * α - 2)).mp
        convert hαref using 1 <;> ring
      exact ⟨2 * α - 2, hnew, by linarith⟩
    · exact ⟨x, hx, lt_of_le_of_ne (hS x hx) (Ne.symm hxzero)⟩
  obtain ⟨x, hx, hxpos⟩ := hpositive
  have hxupper : x < 2 := lt_of_le_of_lt (hbound x hx) hα₂
  have href := hreflectS x hx hxpos hxupper
  obtain ⟨j, hj⟩ := hlattice x hx
  obtain ⟨k, hk⟩ := hlattice (2 - x) href
  have hsum : (2 : ℝ) = ((j + k : ℕ) : ℝ) * (δ / 2) := by
    push_cast
    nlinarith
  have hmpos : 0 < ((j + k : ℕ) : ℝ) := by
    nlinarith
  have hmzero : ((j + k : ℕ) : ℝ) ≠ 0 := ne_of_gt hmpos
  have hαeq : α = alpha (j + k) := by
    have hquot : 2 / ((j + k : ℕ) : ℝ) = 2 - α := by
      apply (div_eq_iff hmzero).mpr
      dsimp [δ] at hsum
      nlinarith
    unfold alpha
    rw [hquot]
    ring
  have hmge : 3 ≤ j + k := by
    by_contra hsmall
    have hle : j + k ≤ 2 := by omega
    have hle' : ((j + k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hle
    dsimp [δ] at hsum
    nlinarith
  exact ⟨j + k, hmge, hαeq⟩

end QuantumBehaviors
