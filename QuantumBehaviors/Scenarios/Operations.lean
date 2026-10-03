import QuantumBehaviors.Scenarios.Basic
import QuantumBehaviors.Projection.FiniteFormula

/-! Polynomial, linear and probability operations for adding and merging outcomes. -/
namespace QuantumBehaviors.Scenarios

open Matrix
open scoped BigOperators Kronecker ComplexOrder

variable {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)

lemma padBinary_map {V W : Type*} [AddCommMonoid V] [AddCommMonoid W] (f : V →+ W)
    (v : Bool → V) (a : Fin m) :
    f (padBinary hm v a) = padBinary hm (fun x => f (v x)) a := by
  unfold padBinary
  split_ifs <;> simp

lemma mergeBinary_map {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W)
    (v : Fin m → V) (a : Bool) :
    f (mergeBinary hm v a) = mergeBinary hm (fun x => f (v x)) a := by
  cases a <;> simp [mergeBinary, map_sum, map_sub]

lemma merge_binary_effect {A : Type*} [Ring A] (v : Fin m → A)
    (hsum : ∑ a, v a = 1) (a : Bool) :
    mergeBinary hm v a = effect (v (outcomeOne hm)) a := by
  cases a <;> simp [mergeBinary, effect, hsum]

lemma pad_effect_sum {A : Type*} [Ring A] (P : A) :
    (∑ a, padBinary hm (effect P) a) = 1 := by
  rw [sum_padBinary]
  simp [effect]

lemma pad_bilinear {V W Z : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (L : V →ₗ[ℂ] W →ₗ[ℂ] Z) (v : Bool → V) (w : Bool → W) (a : Fin m) (b : Fin n) :
    L (padBinary hm v a) (padBinary hn w b) =
      padBinary hm (fun x => padBinary hn (fun y => L (v x) (w y)) b) a := by
  unfold padBinary
  split_ifs <;> simp

lemma merge_bilinear {V W Z : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (L : V →ₗ[ℂ] W →ₗ[ℂ] Z) (v : Fin m → V) (w : Fin n → W) (a b : Bool) :
    mergeBinary hm (fun x => mergeBinary hn (fun y => L (v x) (w y)) b) a =
      L (mergeBinary hm v a) (mergeBinary hn w b) := by
  cases a <;> cases b <;>
    simp [mergeBinary, map_sum, map_sub, LinearMap.sum_apply, LinearMap.sub_apply]
  rw [Finset.sum_comm]
  abel

variable {nA nB mA mB : ℕ}

theorem continuous_extend (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Continuous (extend (nA := nA) (nB := nB) hmA hmB) := by
  apply continuous_pi
  rintro ⟨i, j, a, b⟩
  dsimp [extend, padBinary]
  split_ifs <;> fun_prop

theorem continuous_retract (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Continuous (retract hnA hnB hmA hmB) := by
  apply continuous_pi
  rintro ⟨i, j, a, b⟩
  cases a <;> cases b <;> dsimp [retract, mergeBinary] <;> fun_prop

noncomputable def extendPolynomial (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (x : Coordinate nA nB mA mB) : MvPolynomial QuantumBehaviors.Coordinate ℝ :=
  padBinary hmA (fun a => padBinary hmB
    (fun b => MvPolynomial.X (extendInput x.1, extendInput x.2.1, a, b)) x.2.2.2) x.2.2.1

theorem eval_extendPolynomial (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (p : QuantumBehaviors.Behavior) (x : Coordinate nA nB mA mB) :
    MvPolynomial.eval p (extendPolynomial hmA hmB x) = extend hmA hmB p x := by
  rcases x with ⟨i, j, a, b⟩
  dsimp only [extendPolynomial, extend]
  unfold padBinary
  split_ifs <;> simp_all

theorem semialgebraic_preimage_extend {C : Set (Behavior nA nB mA mB)}
    (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (hC : IsSemialgebraic C) :
    IsSemialgebraic (extend hmA hmB ⁻¹' C) := by
  have h := hC.polynomial_preimage (extendPolynomial hmA hmB)
  simpa only [eval_extendPolynomial] using h

end QuantumBehaviors.Scenarios
