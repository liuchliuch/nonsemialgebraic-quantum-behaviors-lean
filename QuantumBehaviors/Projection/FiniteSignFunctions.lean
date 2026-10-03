import QuantumBehaviors.Projection.UniformGCD
import QuantumBehaviors.Projection.Vendored.SturmChainDefs
import Mathlib.Data.List.OfFn

/-! # Finite computations on rational-expression signs -/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial Sturm
attribute [local instance] Classical.propDecidable

variable {ι α : Type*}

theorem rationallyRepresentable_signFunction [Fintype α] [DecidableEq α]
    (f : α → (ι → ℝ) → ℝ) (hf : ∀ i, RationallyRepresentable (f i))
    (g : (α → SignType) → ℝ) :
    RationallyRepresentable (fun x => g (fun i => SignType.sign (f i x))) := by
  classical
  let C := fun s : α → SignType => {x : ι → ℝ | ∀ i, SignType.sign (f i x) = s i}
  have hC : ∀ s, IsSemialgebraic (C s) := fun s =>
    isSemialgebraic_finite_forall (fun i => {x | SignType.sign (f i x) = s i})
      (fun i => (hf i).isSemialgebraic_sign (s i))
  have hrep : RationallyRepresentable (fun x => ∑ s : α → SignType,
      if x ∈ C s then g s else 0) := by
    apply RationallyRepresentable.finset_sum
    intro s hs
    convert RationallyRepresentable.ite (hC s)
      (RationallyRepresentable.const (g s)) (RationallyRepresentable.const 0) using 1
    funext x
    by_cases hx : x ∈ C s <;> simp only [hx, ite_true, ite_false]
  convert hrep using 1
  funext x
  rw [Finset.sum_eq_single (fun i => SignType.sign (f i x))]
  · have hx : x ∈ C (fun i => SignType.sign (f i x)) := fun _ => rfl
    rw [if_pos hx]
  · intro s hs hne
    have hx : x ∉ C s := fun h => hne (funext h).symm
    rw [if_neg hx]
  · simp

lemma list_forall₂_ofFn {α β : Type*} {n : ℕ} {R : α → β → Prop}
    (f : Fin n → α) (g : Fin n → β) (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

lemma sign_cast_real (s : SignType) : SignType.sign (s : ℝ) = s := by
  cases s <;> norm_num

/-- Zero-skipping sign variations are a finite function of the input signs. -/
theorem rationallyRepresentable_signVariations {n : ℕ}
    (f : Fin n → (ι → ℝ) → ℝ) (hf : ∀ i, RationallyRepresentable (f i)) :
    RationallyRepresentable (fun x => (signVariations (List.ofFn (fun i => f i x)) : ℝ)) := by
  have hrep := rationallyRepresentable_signFunction f hf
    (fun s => (signVariations (List.ofFn (fun i => (s i : ℝ))) : ℝ))
  convert hrep using 1
  funext x
  apply congrArg (fun n : ℕ => (n : ℝ))
  apply signVariations_congr
  apply list_forall₂_ofFn
  intro i
  exact (sign_cast_real _).symm

/-- Padding a list by zeros does not change its filtered nonzero entries. -/
lemma filter_padded_ofFn {α : Type*} (l : List α) (f : α → ℝ) (z : α) (hz : f z = 0)
    (n : ℕ) (hl : l.length ≤ n) :
    (List.ofFn (fun i : Fin n => f (l[i]?.getD z))).filter (fun x => decide (x ≠ 0)) =
      (l.map f).filter (fun x => decide (x ≠ 0)) := by
  induction n generalizing l with
  | zero =>
      have he : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
      simp [he]
  | succ n ih =>
      cases l with
      | nil => simp [hz]
      | cons a l =>
          have hlen : l.length ≤ n := by simpa using hl
          simpa [List.ofFn_succ, List.filter_cons] using
            congrArg (fun t => if f a ≠ 0 then f a :: t else t) (ih l hlen)

lemma signVariations_padded_ofFn {α : Type*} (l : List α) (f : α → ℝ) (z : α) (hz : f z = 0)
    (n : ℕ) (hl : l.length ≤ n) :
    signVariations (List.ofFn (fun i : Fin n => f (l[i]?.getD z))) =
      signVariations (l.map f) := by
  unfold signVariations
  rw [filter_padded_ofFn l f z hz n hl]

end QuantumBehaviors.Projection
