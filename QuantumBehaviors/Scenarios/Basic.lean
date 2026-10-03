import QuantumBehaviors.Scenarios.Definitions
import QuantumBehaviors.Models
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! General finite Bell scenarios and exact input/outcome extension/retraction maps. -/
namespace QuantumBehaviors.Scenarios

open scoped BigOperators Kronecker ComplexOrder

def extendInput {n : ℕ} (i : Fin n) : Input := ⟨min i.val 3, by omega⟩
def originalInput {n : ℕ} (hn : 4 ≤ n) : Input → Fin n := Fin.castLE hn

@[simp] theorem extend_original {n : ℕ} (hn : 4 ≤ n) (i : Input) :
    extendInput (originalInput hn i) = i := by
  apply Fin.ext
  simp [extendInput, originalInput, Nat.min_eq_left (show i.val ≤ 3 by omega)]

def outcomeZero {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨0, by omega⟩
def outcomeOne {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨1, by omega⟩

theorem outcomeZero_ne_one {m : ℕ} (hm : 2 ≤ m) : outcomeZero hm ≠ outcomeOne hm := by
  intro h
  have := congrArg Fin.val h
  simp [outcomeZero, outcomeOne] at this

noncomputable def padBinary {V : Type*} [Zero V] {m : ℕ} (hm : 2 ≤ m)
    (v : Bool → V) (a : Fin m) : V :=
  if a = outcomeZero hm then v false else if a = outcomeOne hm then v true else 0

@[simp] theorem padBinary_zero {V : Type*} [Zero V] {m : ℕ} (hm : 2 ≤ m) (v : Bool → V) :
    padBinary hm v (outcomeZero hm) = v false := by simp [padBinary]

@[simp] theorem padBinary_one {V : Type*} [Zero V] {m : ℕ} (hm : 2 ≤ m) (v : Bool → V) :
    padBinary hm v (outcomeOne hm) = v true := by simp [padBinary, Ne.symm (outcomeZero_ne_one hm)]

theorem sum_padBinary {V : Type*} [AddCommMonoid V] {m : ℕ} (hm : 2 ≤ m) (v : Bool → V) :
    (∑ a, padBinary hm v a) = v false + v true := by
  classical
  have heq : ∀ a, padBinary hm v a =
      (if a = outcomeZero hm then v false else 0) + (if a = outcomeOne hm then v true else 0) := by
    intro a
    by_cases h0 : a = outcomeZero hm
    · subst a
      simp [padBinary, outcomeZero_ne_one hm]
    · simp [padBinary, h0]
  simp only [heq, Finset.sum_add_distrib]
  simp

noncomputable def mergeBinary {V : Type*} [AddCommGroup V] {m : ℕ} (hm : 2 ≤ m)
    (v : Fin m → V) (a : Bool) : V :=
  if a then v (outcomeOne hm) else (∑ b, v b) - v (outcomeOne hm)

@[simp] theorem merge_padBinary {V : Type*} [AddCommGroup V] {m : ℕ} (hm : 2 ≤ m)
    (v : Bool → V) (a : Bool) : mergeBinary hm (padBinary hm v) a = v a := by
  cases a <;> simp [mergeBinary, sum_padBinary]

lemma merge_pad_swap {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {V : Type*} [AddCommGroup V] (v : Bool → Fin n → V)
    (a : Fin m) (b : Bool) :
    mergeBinary hn (fun y => padBinary hm (fun x => v x y) a) b =
      padBinary hm (fun x => mergeBinary hn (v x) b) a := by
  by_cases h0 : a = outcomeZero hm
  · subst a
    simp
  · by_cases h1 : a = outcomeOne hm
    · subst a
      simp
    · cases b <;> simp [padBinary, mergeBinary, h0, h1]

noncomputable def extend {nA nB mA mB : ℕ} (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (p : QuantumBehaviors.Behavior) : Behavior nA nB mA mB :=
  fun ⟨i, j, a, b⟩ => padBinary hmA
    (fun x => padBinary hmB (fun y => p (extendInput i, extendInput j, x, y)) b) a

noncomputable def retract {nA nB mA mB : ℕ}
    (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (p : Behavior nA nB mA mB) : QuantumBehaviors.Behavior :=
  fun ⟨i, j, a, b⟩ => mergeBinary hmA
    (fun x => mergeBinary hmB (fun y => p (originalInput hnA i, originalInput hnB j, x, y)) b) a

@[simp] theorem retract_extend {nA nB mA mB : ℕ}
    (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (p : QuantumBehaviors.Behavior) : retract hnA hnB hmA hmB (extend hmA hmB p) = p := by
  funext x
  rcases x with ⟨i, j, a, b⟩
  simp [retract, extend, merge_pad_swap]

end QuantumBehaviors.Scenarios
