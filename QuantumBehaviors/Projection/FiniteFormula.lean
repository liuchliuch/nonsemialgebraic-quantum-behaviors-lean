import QuantumBehaviors.Geometry
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Finite polynomial-sign formulas

This file supplies explicit syntax operations and finite-Boolean closure. No projection
closure is part of any definition. In particular, `IsSemialgebraic` remains the definition
in `Geometry.lean`, with an actual finite list of real-coefficient polynomials.
-/

noncomputable section

namespace QuantumBehaviors

namespace SignFormula

/-- Rename the atoms in a finite sign formula. -/
def map {ι κ : Type*} (f : ι → κ) : SignFormula ι → SignFormula κ
  | .truth b => .truth b
  | .atom i s => .atom (f i) s
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)
  | .neg p => .neg (p.map f)

@[simp] theorem eval_map {ι κ : Type*} (f : ι → κ) (p : SignFormula ι)
    (v : κ → SignType) : (p.map f).eval v = p.eval (v ∘ f) := by
  induction p <;> simp_all [map, eval, Function.comp_def]

/-- Finite conjunction, including the empty conjunction. -/
def all {ι : Type*} : List (SignFormula ι) → SignFormula ι
  | [] => .truth true
  | p :: ps => .conj p (all ps)

/-- Finite disjunction, including the empty disjunction. -/
def any {ι : Type*} : List (SignFormula ι) → SignFormula ι
  | [] => .truth false
  | p :: ps => .disj p (any ps)

@[simp] theorem eval_all {ι : Type*} (ps : List (SignFormula ι)) (v : ι → SignType) :
    (all ps).eval v = true ↔ ∀ p ∈ ps, p.eval v = true := by
  induction ps with
  | nil => simp [all, eval]
  | cons p ps ih => simp [all, eval, ih]

@[simp] theorem eval_any {ι : Type*} (ps : List (SignFormula ι)) (v : ι → SignType) :
    (any ps).eval v = true ↔ ∃ p ∈ ps, p.eval v = true := by
  induction ps with
  | nil => simp [any, eval]
  | cons p ps ih => simp [any, eval, ih]

/-- Compile an arbitrary finite truth table into literal finite Boolean sign syntax. -/
def table {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → SignType) → Bool) : SignFormula ι :=
  any (Finset.univ.toList.map fun s : ι → SignType =>
    .conj (.truth (f s)) (all (Finset.univ.toList.map fun i => .atom i (s i))))

@[simp] theorem eval_table {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → SignType) → Bool) (v : ι → SignType) : (table f).eval v = f v := by
  have h : (table f).eval v = true ↔ f v = true := by
    rw [table, eval_any]
    constructor
    · rintro ⟨p, hp, hpv⟩
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hp
      simp only [eval, Bool.and_eq_true, eval_all] at hpv
      have heq : v = s := by
        funext i
        have hi := hpv.2 (.atom i (s i)) (List.mem_map.mpr ⟨i, by simp, rfl⟩)
        simpa [eval] using hi
      simpa [heq] using hpv.1
    · intro hv
      refine ⟨_, List.mem_map.mpr ⟨v, by simp, rfl⟩, ?_⟩
      simp only [eval, Bool.and_eq_true, eval_all]
      refine ⟨hv, ?_⟩
      intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      simp [eval]
  cases h₁ : (table f).eval v <;> cases h₂ : f v <;> simp_all

/-- Every formula, even with atoms in an infinite type, uses an explicit finite atom list. -/
theorem exists_finite_atoms {ι : Type*} (p : SignFormula ι) :
    ∃ (n : ℕ) (f : Fin n → ι) (q : SignFormula (Fin n)),
      ∀ v : ι → SignType, q.eval (v ∘ f) = p.eval v := by
  induction p with
  | truth b => exact ⟨0, Fin.elim0, .truth b, fun _ => rfl⟩
  | atom i s => exact ⟨1, fun _ => i, .atom 0 s, fun _ => rfl⟩
  | conj p q hp hq =>
      obtain ⟨n, f, p', hp'⟩ := hp
      obtain ⟨m, g, q', hq'⟩ := hq
      refine ⟨n + m, Fin.addCases f g,
        .conj (p'.map (Fin.castAdd m)) (q'.map (Fin.natAdd n)), ?_⟩
      intro v
      simpa [eval, Function.comp_def] using congrArg₂ (fun a b : Bool => a && b) (hp' v) (hq' v)
  | disj p q hp hq =>
      obtain ⟨n, f, p', hp'⟩ := hp
      obtain ⟨m, g, q', hq'⟩ := hq
      refine ⟨n + m, Fin.addCases f g,
        .disj (p'.map (Fin.castAdd m)) (q'.map (Fin.natAdd n)), ?_⟩
      intro v
      simpa [eval, Function.comp_def] using congrArg₂ (fun a b : Bool => a || b) (hp' v) (hq' v)
  | neg p hp =>
      obtain ⟨n, f, p', hp'⟩ := hp
      exact ⟨n, f, .neg p', fun v => by simp [eval, hp']⟩

end SignFormula

/-- A convenient syntax whose atoms are the polynomials themselves. It is still finite syntax. -/
abbrev PolynomialSignFormula (ι : Type*) := SignFormula (MvPolynomial ι ℝ)

/-- Evaluate a polynomial-sign formula at a real point. -/
def PolynomialSignFormula.realize {ι : Type*} (p : PolynomialSignFormula ι)
    (x : ι → ℝ) : Bool := p.eval (fun f => SignType.sign (MvPolynomial.eval x f))

/-- Exact equivalence with the original finite-list definition, not a definition by closure. -/
theorem isSemialgebraic_iff_formula {ι : Type*} {C : Set (ι → ℝ)} :
    IsSemialgebraic C ↔ ∃ p : PolynomialSignFormula ι,
      ∀ x, x ∈ C ↔ p.realize x = true := by
  constructor
  · rintro ⟨n, f, p, hp⟩
    refine ⟨p.map f, ?_⟩
    intro x
    simpa [PolynomialSignFormula.realize, Function.comp_def] using hp x
  · rintro ⟨p, hp⟩
    obtain ⟨n, f, q, hq⟩ := p.exists_finite_atoms
    refine ⟨n, f, q, ?_⟩
    intro x
    rw [hp]
    change p.eval (fun f => SignType.sign (MvPolynomial.eval x f)) = true ↔ _
    rw [← hq]
    rfl

namespace IsSemialgebraic

variable {ι κ : Type*} {C D : Set (ι → ℝ)}

theorem univ : IsSemialgebraic (Set.univ : Set (ι → ℝ)) :=
  isSemialgebraic_iff_formula.mpr ⟨.truth true, fun _ => by simp [PolynomialSignFormula.realize,
    SignFormula.eval]⟩

theorem empty : IsSemialgebraic (∅ : Set (ι → ℝ)) :=
  isSemialgebraic_iff_formula.mpr ⟨.truth false, fun _ => by simp [PolynomialSignFormula.realize,
    SignFormula.eval]⟩

theorem compl (hC : IsSemialgebraic C) : IsSemialgebraic Cᶜ := by
  obtain ⟨p, hp⟩ := isSemialgebraic_iff_formula.mp hC
  refine isSemialgebraic_iff_formula.mpr ⟨.neg p, ?_⟩
  intro x
  simp [PolynomialSignFormula.realize, SignFormula.eval, hp]

theorem inter (hC : IsSemialgebraic C) (hD : IsSemialgebraic D) :
    IsSemialgebraic (C ∩ D) := by
  obtain ⟨p, hp⟩ := isSemialgebraic_iff_formula.mp hC
  obtain ⟨q, hq⟩ := isSemialgebraic_iff_formula.mp hD
  refine isSemialgebraic_iff_formula.mpr ⟨.conj p q, ?_⟩
  intro x
  simp [PolynomialSignFormula.realize, SignFormula.eval, hp, hq]

theorem union (hC : IsSemialgebraic C) (hD : IsSemialgebraic D) :
    IsSemialgebraic (C ∪ D) := by
  obtain ⟨p, hp⟩ := isSemialgebraic_iff_formula.mp hC
  obtain ⟨q, hq⟩ := isSemialgebraic_iff_formula.mp hD
  refine isSemialgebraic_iff_formula.mpr ⟨.disj p q, ?_⟩
  intro x
  simp [PolynomialSignFormula.realize, SignFormula.eval, hp, hq]

/-- Pullback along an arbitrary polynomial map: explicit atom substitution. -/
theorem polynomial_preimage (hC : IsSemialgebraic C) (f : ι → MvPolynomial κ ℝ) :
    IsSemialgebraic {x : κ → ℝ | (fun i => MvPolynomial.eval x (f i)) ∈ C} := by
  obtain ⟨n, p, φ, hφ⟩ := hC
  refine ⟨n, fun i => MvPolynomial.eval₂ MvPolynomial.C f (p i), φ, ?_⟩
  intro x
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ := by
    ext r
    simp
  simpa only [Set.mem_setOf_eq, MvPolynomial.eval_eval₂, hcomp] using
    hφ (fun i => MvPolynomial.eval x (f i))

/-- Every single polynomial-sign condition is semialgebraic. -/
theorem sign (p : MvPolynomial ι ℝ) (s : SignType) :
    IsSemialgebraic {x : ι → ℝ | SignType.sign (MvPolynomial.eval x p) = s} := by
  refine isSemialgebraic_iff_formula.mpr ⟨.atom p s, ?_⟩
  intro x
  simp [PolynomialSignFormula.realize, SignFormula.eval]

end IsSemialgebraic

end QuantumBehaviors
