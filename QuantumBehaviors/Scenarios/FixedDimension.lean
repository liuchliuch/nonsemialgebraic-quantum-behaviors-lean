import QuantumBehaviors.Scenarios.PolynomialMatrices
import QuantumBehaviors.Scenarios.Basic

/-! Fixed finite density-matrix/POVM Born realizations form genuine semialgebraic sets. -/
namespace QuantumBehaviors.Scenarios
open Matrix Set
open scoped BigOperators Kronecker ComplexOrder

abbrev StrategyCoordinate (nA nB mA mB dA dB : ℕ) :=
  ((Fin dA × Fin dB) × (Fin dA × Fin dB) × Bool) ⊕
  (Fin nA × Fin mA × Fin dA × Fin dA × Bool) ⊕
  (Fin nB × Fin mB × Fin dB × Fin dB × Bool)

variable {nA nB mA mB dA dB : ℕ}
abbrev Parameters := StrategyCoordinate nA nB mA mB dA dB → ℝ

def parameterDensity (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  fun i j => ⟨z (Sum.inl (i,j,false)),z (Sum.inl (i,j,true))⟩

def parameterAlice (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB))
    (i : Fin nA) (a : Fin mA) : Matrix (Fin dA) (Fin dA) ℂ :=
  fun r s => ⟨z (Sum.inr (Sum.inl (i,a,r,s,false))),z (Sum.inr (Sum.inl (i,a,r,s,true)))⟩

def parameterBob (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB))
    (j : Fin nB) (b : Fin mB) : Matrix (Fin dB) (Fin dB) ℂ :=
  fun r s => ⟨z (Sum.inr (Sum.inr (j,b,r,s,false))),z (Sum.inr (Sum.inr (j,b,r,s,true)))⟩

noncomputable def ParameterConstraints (p : Behavior nA nB mA mB) (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) : Prop :=
  (parameterDensity z).PosSemidef ∧ (parameterDensity z).trace = 1 ∧
  (∀ i a, (parameterAlice z i a).PosSemidef) ∧ (∀ i, ∑ a, parameterAlice z i a = 1) ∧
  (∀ j b, (parameterBob z j b).PosSemidef) ∧ (∀ j, ∑ b, parameterBob z j b = 1) ∧
  ∀ i j a b, (p (i,j,a,b) : ℂ) =
    (parameterDensity z * (parameterAlice z i a ⊗ₖ parameterBob z j b)).trace

def FixedDimensionSet (nA nB mA mB dA dB : ℕ) : Set (Behavior nA nB mA mB) :=
  {p | ∃ s : FiniteStrategy nA nB mA mB dA dB, s.realizes p}

lemma fixed_dimension_parameters (p : Behavior nA nB mA mB) :
    p ∈ FixedDimensionSet nA nB mA mB dA dB ↔ ∃ z, ParameterConstraints (dA := dA) (dB := dB) p z := by
  constructor
  · rintro ⟨s,hs⟩
    let z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) :=
      Sum.elim (fun c => if c.2.2 then (s.density c.1 c.2.1).im else (s.density c.1 c.2.1).re)
        (Sum.elim (fun c => if c.2.2.2.2 then (s.alice c.1 c.2.1 c.2.2.1 c.2.2.2.1).im else (s.alice c.1 c.2.1 c.2.2.1 c.2.2.2.1).re)
          (fun c => if c.2.2.2.2 then (s.bob c.1 c.2.1 c.2.2.1 c.2.2.2.1).im else (s.bob c.1 c.2.1 c.2.2.1 c.2.2.2.1).re))
    have hρ : parameterDensity z = s.density := by ext i j <;> rfl
    have hA : ∀ i a, parameterAlice z i a = s.alice i a := by intro i a; ext r t <;> rfl
    have hB : ∀ j b, parameterBob z j b = s.bob j b := by intro j b; ext r t <;> rfl
    refine ⟨z,?_⟩
    simp only [ParameterConstraints,hρ,hA,hB]
    exact ⟨s.density_pos,s.density_trace,s.alice_pos,s.alice_sum,s.bob_pos,s.bob_sum,hs⟩
  · rintro ⟨z,hρ,htr,hA,hAs,hB,hBs,hreal⟩
    exact ⟨⟨parameterDensity z,hρ,htr,parameterAlice z,parameterBob z,hA,hAs,hB,hBs⟩,hreal⟩

/-- Semialgebraicity is derived from explicit finite real polynomial coordinates and proved QE. -/
theorem fixed_dimension_semialgebraic (nA nB mA mB dA dB : ℕ) :
    IsSemialgebraic (FixedDimensionSet nA nB mA mB dA dB) := by
  let V := Coordinate nA nB mA mB ⊕ StrategyCoordinate nA nB mA mB dA dB
  let D := fun x : V → ℝ => parameterDensity (x ∘ Sum.inr)
  let A := fun x : V → ℝ => parameterAlice (x ∘ Sum.inr)
  let B := fun x : V → ℝ => parameterBob (x ∘ Sum.inr)
  have hD : ∀ i j, IsComplexPolynomial (fun x => D x i j) := fun i j =>
    IsComplexPolynomial.complex_coord _ _
  have hA : ∀ i a r s, IsComplexPolynomial (fun x => A x i a r s) := fun i a r s =>
    IsComplexPolynomial.complex_coord _ _
  have hB : ∀ j b r s, IsComplexPolynomial (fun x => B x j b r s) := fun j b r s =>
    IsComplexPolynomial.complex_coord _ _
  have hPSD := polynomial_matrix_psd D hD
  have htrace : IsSemialgebraic {x | (D x).trace = 1} :=
    (IsComplexPolynomial.sum_fintype _ (fun i => hD i i)).eq_semialgebraic (IsComplexPolynomial.const 1)
  have hAP : IsSemialgebraic {x | ∀ i a, (A x i a).PosSemidef} :=
    IsSemialgebraic.forall_finite _ fun i => IsSemialgebraic.forall_finite _ fun a =>
      polynomial_matrix_psd (fun x => A x i a) (hA i a)
  have hBP : IsSemialgebraic {x | ∀ j b, (B x j b).PosSemidef} :=
    IsSemialgebraic.forall_finite _ fun j => IsSemialgebraic.forall_finite _ fun b =>
      polynomial_matrix_psd (fun x => B x j b) (hB j b)
  have hAS : IsSemialgebraic {x | ∀ i, ∑ a, A x i a = 1} := by
    apply IsSemialgebraic.forall_finite
    intro i
    apply polynomial_matrix_eq
    · intro r s
      simpa only [Matrix.sum_apply] using IsComplexPolynomial.sum_fintype _ (fun a => hA i a r s)
    · intro r s
      exact IsComplexPolynomial.const _
  have hBS : IsSemialgebraic {x | ∀ j, ∑ b, B x j b = 1} := by
    apply IsSemialgebraic.forall_finite
    intro j
    apply polynomial_matrix_eq
    · intro r s
      simpa only [Matrix.sum_apply] using IsComplexPolynomial.sum_fintype _ (fun b => hB j b r s)
    · intro r s
      exact IsComplexPolynomial.const _
  have hBorn : IsSemialgebraic {x : V → ℝ | ∀ i j a b,
      (x (Sum.inl (i,j,a,b)) : ℂ) = (D x * (A x i a ⊗ₖ B x j b)).trace} := by
    apply IsSemialgebraic.forall_finite
    intro i
    apply IsSemialgebraic.forall_finite
    intro j
    apply IsSemialgebraic.forall_finite
    intro a
    apply IsSemialgebraic.forall_finite
    intro b
    apply (IsComplexPolynomial.coord _).eq_semialgebraic
    change IsComplexPolynomial (fun x => ∑ k, ∑ l, D x k l * (A x i a l.1 k.1 * B x j b l.2 k.2))
    apply IsComplexPolynomial.sum_fintype
    intro k
    apply IsComplexPolynomial.sum_fintype
    intro l
    exact (hD k l).mul ((hA i a l.1 k.1).mul (hB j b l.2 k.2))
  let Z : Set (V → ℝ) := {x | ParameterConstraints (x ∘ Sum.inl) (x ∘ Sum.inr)}
  have hZ : IsSemialgebraic Z := hPSD.inter (htrace.inter (hAP.inter (hAS.inter (hBP.inter (hBS.inter hBorn)))))
  have hproj := hZ.project
  have heq : FixedDimensionSet nA nB mA mB dA dB =
      {p | ∃ z, Sum.elim p z ∈ Z} := by
    ext p
    exact fixed_dimension_parameters p
  rwa [← heq] at hproj

end QuantumBehaviors.Scenarios
