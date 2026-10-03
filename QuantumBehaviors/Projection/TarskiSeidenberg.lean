import QuantumBehaviors.Projection.EliminateOne
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Tarski–Seidenberg for genuine finite polynomial-sign descriptions

One-coordinate elimination is proved through the constructed Tarski-query algorithm and
then iterated over any finite auxiliary coordinate type. `IsSemialgebraic` throughout is
the original finite Boolean polynomial-sign definition from `Geometry.lean`.
-/

noncomputable section

namespace QuantumBehaviors

namespace IsSemialgebraic

/-- Coordinate pullback is an explicit polynomial substitution. -/
theorem coordinate_preimage {ι κ : Type*} {C : Set (ι → ℝ)} (hC : IsSemialgebraic C)
    (f : ι → κ) : IsSemialgebraic {x : κ → ℝ | (fun i => x (f i)) ∈ C} := by
  simpa only [MvPolynomial.eval_X] using hC.polynomial_preimage (fun i => MvPolynomial.X (f i))

/-- Eliminate the `none` coordinate of a finite polynomial-sign formula. -/
theorem project_option {ι : Type*} {Z : Set (Option ι → ℝ)} (hZ : IsSemialgebraic Z) :
    IsSemialgebraic {x : ι → ℝ | ∃ t : ℝ, (fun i => Option.elim i t x) ∈ Z} := by
  obtain ⟨n, f, φ, hφ⟩ := hZ
  have h := Projection.isSemialgebraic_exists_polynomial
    (fun i => MvPolynomial.optionEquivLeft ℝ ι (f i)) φ
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  apply exists_congr
  intro t
  rw [hφ]
  simp only [MvPolynomial.optionEquivLeft_elim_eval]

private def finStepCoordinate (ι : Type*) (n : ℕ) : ι ⊕ Fin (n + 1) → Option (ι ⊕ Fin n)
  | .inl i => some (.inl i)
  | .inr j => Fin.cases none (fun k => some (.inr k)) j

private lemma finStepValue {ι : Type*} (n : ℕ) (x : ι → ℝ) (z : Fin n → ℝ) (t : ℝ) :
    (fun i => Option.elim (finStepCoordinate ι n i) t (Sum.elim x z)) =
      Sum.elim x (Fin.cases t z) := by
  funext i
  cases i with
  | inl i => rfl
  | inr j => exact Fin.cases rfl (fun _ => rfl) j

/-- Eliminate a finite list of arbitrary real auxiliary variables. -/
theorem project_fin {ι : Type*} (n : ℕ) {Z : Set ((ι ⊕ Fin n) → ℝ)}
    (hZ : IsSemialgebraic Z) :
    IsSemialgebraic {x : ι → ℝ | ∃ z : Fin n → ℝ, Sum.elim x z ∈ Z} := by
  induction n with
  | zero =>
      have h := hZ.coordinate_preimage (Sum.elim id Fin.elim0)
      convert h using 1
      ext x
      constructor
      · rintro ⟨z, hz⟩
        have heq : Sum.elim x z = (fun i => x (Sum.elim id Fin.elim0 i)) := by
          funext i
          cases i with
          | inl i => rfl
          | inr j => exact Fin.elim0 j
        simpa only [heq] using hz
      · intro hx
        refine ⟨Fin.elim0, ?_⟩
        have heq : Sum.elim x (Fin.elim0 : Fin 0 → ℝ) =
            (fun i => x (Sum.elim id Fin.elim0 i)) := by
          funext i
          cases i with
          | inl i => rfl
          | inr j => exact Fin.elim0 j
        simpa only [heq] using hx
  | succ n ih =>
      have hW := hZ.coordinate_preimage (finStepCoordinate ι n)
      have hA := hW.project_option
      have h := ih hA
      convert h using 1
      ext x
      change (∃ z : Fin (n + 1) → ℝ, Sum.elim x z ∈ Z) ↔
        ∃ z : Fin n → ℝ, ∃ t : ℝ,
          (fun i => Option.elim (finStepCoordinate ι n i) t (Sum.elim x z)) ∈ Z
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨fun i => z i.succ, z 0, ?_⟩
        rw [finStepValue]
        have heq : Fin.cases (z 0) (fun i => z i.succ) = z := by
          funext j
          exact Fin.cases rfl (fun _ => rfl) j
        simpa only [heq] using hz
      · rintro ⟨z, t, hz⟩
        exact ⟨Fin.cases t z, by simpa only [finStepValue] using hz⟩

/-- **Tarski–Seidenberg:** finite coordinate projections preserve genuine semialgebraicity. -/
theorem project {ι κ : Type*} [Finite κ] {Z : Set ((ι ⊕ κ) → ℝ)}
    (hZ : IsSemialgebraic Z) :
    IsSemialgebraic {x : ι → ℝ | ∃ z : κ → ℝ, Sum.elim x z ∈ Z} := by
  classical
  letI := Fintype.ofFinite κ
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hW := hZ.coordinate_preimage (Sum.map id e.symm)
  have h := hW.project_fin (Fintype.card κ)
  convert h using 1
  ext x
  change (∃ z : κ → ℝ, Sum.elim x z ∈ Z) ↔
    ∃ z : Fin (Fintype.card κ) → ℝ,
      (fun i => Sum.elim x z (Sum.map id e.symm i)) ∈ Z
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨fun j => z (e j), ?_⟩
    have heq : (fun i => Sum.elim x (fun j => z (e j)) (Sum.map id e.symm i)) =
        Sum.elim x z := by
      funext i
      cases i <;> simp
    simpa only [heq] using hz
  · rintro ⟨z, hz⟩
    refine ⟨fun k => z (e.symm k), ?_⟩
    have heq : (fun i => Sum.elim x z (Sum.map id e.symm i)) =
        Sum.elim x (fun k => z (e.symm k)) := by
      funext i
      cases i <;> rfl
    simpa only [heq] using hz

end IsSemialgebraic

/-- A finite quantifier-free output formula for any given finite semialgebraic lift. -/
def projectionFormula {ι κ : Type*} [Finite κ] {Z : Set ((ι ⊕ κ) → ℝ)}
    (hZ : IsSemialgebraic Z) : PolynomialSignFormula ι :=
  (isSemialgebraic_iff_formula.mp hZ.project).choose

/-- The output syntax describes exactly the existential projection. -/
theorem projectionFormula_correct {ι κ : Type*} [Finite κ] {Z : Set ((ι ⊕ κ) → ℝ)}
    (hZ : IsSemialgebraic Z) (x : ι → ℝ) :
    (projectionFormula hZ).realize x = true ↔ ∃ z : κ → ℝ, Sum.elim x z ∈ Z :=
  ((isSemialgebraic_iff_formula.mp hZ.project).choose_spec x).symm

end QuantumBehaviors
