import QuantumBehaviors.ComplexSemidefinite

/-! Explicit finite affine syntax and finite-index coordinate changes for semidefinite lifts. -/
namespace QuantumBehaviors
open scoped BigOperators ComplexOrder
namespace AffineScalar
variable {V W : Type*}

def const (c : ℝ) : AffineScalar V := ⟨c,fun _ => 0⟩
noncomputable def coord [DecidableEq V] (v : V) : AffineScalar V := ⟨0,fun w => if w=v then 1 else 0⟩
def add (a b : AffineScalar V) : AffineScalar V := ⟨a.constant+b.constant,fun v => a.coefficient v+b.coefficient v⟩
def sub (a b : AffineScalar V) : AffineScalar V := ⟨a.constant-b.constant,fun v => a.coefficient v-b.coefficient v⟩
def reindex (e : V ≃ W) (a : AffineScalar V) : AffineScalar W := ⟨a.constant,fun w => a.coefficient (e.symm w)⟩

@[simp] lemma eval_const [Fintype V] (c : ℝ) (x : V → ℝ) : (const c).eval x=c := by simp [const,eval]
@[simp] lemma eval_coord [Fintype V] [DecidableEq V] (v : V) (x : V → ℝ) : (coord v).eval x=x v := by simp [coord,eval]
@[simp] lemma eval_add [Fintype V] (a b : AffineScalar V) (x : V → ℝ) : (add a b).eval x=a.eval x+b.eval x := by
  simp [add,eval,add_mul,Finset.sum_add_distrib]
  ring
@[simp] lemma eval_sub [Fintype V] (a b : AffineScalar V) (x : V → ℝ) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,eval,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] lemma eval_reindex [Fintype V] [Fintype W] (e : V ≃ W) (a : AffineScalar V) (x : W → ℝ) :
    (reindex e a).eval x=a.eval (x ∘ e) := by
  unfold reindex eval
  congr 1
  simpa only [Equiv.symm_apply_apply,Function.comp_apply] using
    (Equiv.sum_comp e (fun w => a.coefficient (e.symm w)*x w)).symm
end AffineScalar

noncomputable def ComplexAffineMatrix.reindexVariables {V W : Type*} {n : ℕ}
    (e : V ≃ W) (A : ComplexAffineMatrix V n) : ComplexAffineMatrix W n :=
  fun c => AffineScalar.reindex e (A c)

@[simp] lemma ComplexAffineMatrix.eval_reindexVariables {V W : Type*} [Fintype V] [Fintype W] {n : ℕ}
    (e : V ≃ W) (A : ComplexAffineMatrix V n) (x : W → ℝ) :
    (A.reindexVariables e).eval x=A.eval (x ∘ e) := by
  ext i j <;> simp [ComplexAffineMatrix.eval,ComplexAffineMatrix.reindexVariables,complexMatrix]

/-- Arbitrary finite auxiliary/equality index types really give the natural-number SDP interface. -/
theorem HasFiniteComplexSDPLift.of_finite {Z J : Type*} [Fintype Z] [Fintype J]
    {C : Set Behavior} {n : ℕ} (A : ComplexAffineMatrix (Coordinate ⊕ Z) n)
    (L : J → AffineScalar (Coordinate ⊕ Z))
    (hC : ∀ p, p ∈ C ↔ ∃ z : Z → ℝ, (A.eval (Sum.elim p z)).PosSemidef ∧
      ∀ j, (L j).eval (Sum.elim p z)=0) : HasFiniteComplexSDPLift C := by
  classical
  let eZ := Fintype.equivFin Z
  let eJ := Fintype.equivFin J
  let e : (Coordinate ⊕ Z) ≃ (Coordinate ⊕ Fin (Fintype.card Z)) := Equiv.sumCongr (Equiv.refl _) eZ
  refine ⟨Fintype.card Z,1,Fintype.card J,(fun _ => n),
    (fun _ => A.reindexVariables e),(fun j => AffineScalar.reindex e (L (eJ.symm j))),?_⟩
  intro p
  rw [hC p]
  constructor
  · rintro ⟨z,hA,hL⟩
    refine ⟨z ∘ eZ.symm,?_,?_⟩
    · intro i
      rw [ComplexAffineMatrix.eval_reindexVariables]
      have heq : Sum.elim p (z ∘ eZ.symm) ∘ e=Sum.elim p z := by funext x;cases x <;> simp [e]
      rwa [heq]
    · intro j
      rw [AffineScalar.eval_reindex]
      have heq : Sum.elim p (z ∘ eZ.symm) ∘ e=Sum.elim p z := by funext x;cases x <;> simp [e]
      rw [heq]
      exact hL _
  · rintro ⟨z,hA,hL⟩
    refine ⟨z ∘ eZ,?_,?_⟩
    · have h := hA (0 : Fin 1)
      rw [ComplexAffineMatrix.eval_reindexVariables] at h
      have heq : Sum.elim p z ∘ e=Sum.elim p (z ∘ eZ) := by funext x;cases x <;> rfl
      rwa [heq] at h
    · intro j
      have h := hL (eJ j)
      rw [AffineScalar.eval_reindex,Equiv.symm_apply_apply] at h
      have heq : Sum.elim p z ∘ e=Sum.elim p (z ∘ eZ) := by funext x;cases x <;> rfl
      rwa [heq] at h

theorem HasFiniteSemialgebraicLift.semialgebraic {C : Set Behavior} (h : HasFiniteSemialgebraicLift C) :
    IsSemialgebraic C := by
  obtain ⟨r,Z,hZ,hC⟩ := h
  have heq : C={p | ∃ z : Fin r → ℝ,Sum.elim p z ∈ Z} := Set.ext hC
  rw [heq]
  exact hZ.project

theorem HasFiniteComplexSDPLift.semialgebraic {C : Set Behavior} (h : HasFiniteComplexSDPLift C) :
    IsSemialgebraic C := h.to_semialgebraic_lift.semialgebraic

end QuantumBehaviors
