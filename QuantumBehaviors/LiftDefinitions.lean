import QuantumBehaviors.Definitions

/-! Finite semialgebraic and real/complex semidefinite lifts, with arbitrary real data. -/
namespace QuantumBehaviors
open scoped BigOperators ComplexOrder

/-- A finite semialgebraic lift uses finitely many auxiliary real coordinates. -/
def HasFiniteSemialgebraicLift (C : Set Behavior) : Prop :=
  ∃ (r : ℕ) (Z : Set ((Coordinate ⊕ Fin r) → ℝ)), IsSemialgebraic Z ∧
    ∀ p, p ∈ C ↔ ∃ z : Fin r → ℝ, Sum.elim p z ∈ Z

structure AffineScalar (V : Type*) where
  constant : ℝ
  coefficient : V → ℝ

noncomputable def AffineScalar.eval {V : Type*} [Fintype V] (a : AffineScalar V) (x : V → ℝ) : ℝ :=
  a.constant + ∑ v, a.coefficient v * x v

abbrev AffineMatrix (V : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) (AffineScalar V)

noncomputable def AffineMatrix.eval {V : Type*} [Fintype V] {n : ℕ}
    (A : AffineMatrix V n) (x : V → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j).eval x

/-- Standard finite real semidefinite lifts, including affine equalities and arbitrary real data. -/
def HasFiniteSDPLift (C : Set Behavior) : Prop :=
  ∃ (r k e : ℕ) (size : Fin k → ℕ)
    (A : ∀ i, AffineMatrix (Coordinate ⊕ Fin r) (size i))
    (L : Fin e → AffineScalar (Coordinate ⊕ Fin r)),
    ∀ p, p ∈ C ↔ ∃ z : Fin r → ℝ,
      (∀ i, (A i |>.eval (Sum.elim p z)).PosSemidef) ∧
      ∀ j, (L j).eval (Sum.elim p z) = 0

abbrev ComplexMatrixCoordinate (n : ℕ) := Fin n × Fin n × Bool

def complexMatrix {n : ℕ} (x : ComplexMatrixCoordinate n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ⟨x (i,j,false), x (i,j,true)⟩

abbrev ComplexAffineMatrix (V : Type*) (n : ℕ) := ComplexMatrixCoordinate n → AffineScalar V

noncomputable def ComplexAffineMatrix.eval {V : Type*} [Fintype V] {n : ℕ}
    (A : ComplexAffineMatrix V n) (x : V → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  complexMatrix (fun c => (A c).eval x)

/-- Finite complex-Hermitian LMIs; affine equalities are expressed on real coordinates. -/
def HasFiniteComplexSDPLift (C : Set Behavior) : Prop :=
  ∃ (r k e : ℕ) (size : Fin k → ℕ)
    (A : ∀ i, ComplexAffineMatrix (Coordinate ⊕ Fin r) (size i))
    (L : Fin e → AffineScalar (Coordinate ⊕ Fin r)),
    ∀ p, p ∈ C ↔ ∃ z : Fin r → ℝ,
      (∀ i, (A i |>.eval (Sum.elim p z)).PosSemidef) ∧
      ∀ j, (L j).eval (Sum.elim p z) = 0

end QuantumBehaviors
