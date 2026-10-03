import QuantumBehaviors.Projection.AffineSampling

/-!
# Explicit one-variable affine sign elimination

The eliminated variable may occur affinely, with arbitrary polynomial dependence on all
remaining real variables. The output is an actual finite quantifier-free sign formula.
This is a restricted projection theorem; it does not claim nonlinear Tarski–Seidenberg.
-/

noncomputable section

namespace QuantumBehaviors.Projection

variable {ι κ : Type*}

/-- The finite atom inventory used by affine elimination. -/
abbrev AffineAtom (ι : Type*) := ι ⊕ (ι ⊕ (ι × ι))

/-- Coefficients and all pairwise affine resultants. -/
def affineAtoms (a b : ι → MvPolynomial κ ℝ) : AffineAtom ι → MvPolynomial κ ℝ
  | .inl i => a i
  | .inr (.inl i) => b i
  | .inr (.inr (i, j)) => a i * b j - a j * b i

/-- The same finite inventory evaluated over real coefficients. -/
def affineSigns (a b : ι → ℝ) : AffineAtom ι → SignType
  | .inl i => SignType.sign (a i)
  | .inr (.inl i) => SignType.sign (b i)
  | .inr (.inr (i, j)) => SignType.sign (a i * b j - a j * b i)

def botFromSigns (v : AffineAtom ι → SignType) (j : ι) : SignType :=
  if v (.inl j) = 0 then v (.inr (.inl j)) else -v (.inl j)

def rootFromSigns (v : AffineAtom ι → SignType) (i j : ι) : SignType :=
  v (.inl i) * v (.inr (.inr (i, j)))

def rightFromSigns (v : AffineAtom ι → SignType) (i j : ι) : SignType :=
  if rootFromSigns v i j = 0 then v (.inl j) else rootFromSigns v i j

/-- A finite Boolean computation on coefficient/resultant signs. -/
def affineDecision [Fintype ι] (φ : SignFormula ι) (v : AffineAtom ι → SignType) : Bool :=
  φ.eval (botFromSigns v) || decide (∃ i, v (.inl i) ≠ 0 ∧
    (φ.eval (rootFromSigns v i) = true ∨ φ.eval (rightFromSigns v i) = true))

lemma sign_div_real (x y : ℝ) : SignType.sign (x / y) = SignType.sign x * SignType.sign y := by
  rw [div_eq_mul_inv, sign_mul]
  congr 1
  rcases lt_trichotomy y 0 with h | h | h <;> simp [h]

@[simp] lemma botFromSigns_affineSigns (a b : ι → ℝ) (j : ι) :
    botFromSigns (affineSigns a b) j = affineBotSign (a j) (b j) := by
  simp [botFromSigns, affineSigns, affineBotSign, sign_eq_zero_iff]

lemma rootFromSigns_affineSigns (a b : ι → ℝ) {i : ι} (ha : a i ≠ 0) (j : ι) :
    rootFromSigns (affineSigns a b) i j =
      SignType.sign (a j * affineRoot (a i) (b i) + b j) := by
  have heq : a j * affineRoot (a i) (b i) + b j = (a i * b j - a j * b i) / a i := by
    dsimp [affineRoot]
    field_simp
    <;> ring
  rw [heq, sign_div_real]
  simp [rootFromSigns, affineSigns, mul_comm]

lemma rightFromSigns_affineSigns (a b : ι → ℝ) {i : ι} (ha : a i ≠ 0) (j : ι) :
    rightFromSigns (affineSigns a b) i j =
      affineRightSign (a j) (b j) (affineRoot (a i) (b i)) := by
  simp [rightFromSigns, rootFromSigns_affineSigns a b ha, affineSigns,
    affineRightSign, sign_eq_zero_iff]

/-- Exact semantic correctness of the finite affine decision table. -/
theorem affineDecision_correct [Fintype ι] (a b : ι → ℝ) (φ : SignFormula ι) :
    (∃ t : ℝ, φ.eval (fun i => SignType.sign (a i * t + b i)) = true) ↔
      affineDecision φ (affineSigns a b) = true := by
  classical
  simp only [affineDecision, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht⟩
    rcases affine_sign_sampling a b t with hbot | ⟨i, hi, hroot | hright⟩
    · left
      convert ht using 1
      congr 1
      funext j
      exact (botFromSigns_affineSigns a b j).trans (hbot j).symm
    · right
      refine ⟨i, ?_, Or.inl ?_⟩
      · simpa [affineSigns, sign_eq_zero_iff] using hi
      · convert ht using 1
        congr 1
        funext j
        exact (rootFromSigns_affineSigns a b hi j).trans (hroot j).symm
    · right
      refine ⟨i, ?_, Or.inr ?_⟩
      · simpa [affineSigns, sign_eq_zero_iff] using hi
      · convert ht using 1
        congr 1
        funext j
        exact (rightFromSigns_affineSigns a b hi j).trans (hright j).symm
  · rintro (hbot | ⟨i, hi, hroot | hright⟩)
    · obtain ⟨t, ht⟩ := affine_bot_sign_realized a b
      refine ⟨t, ?_⟩
      convert hbot using 1
      congr 1
      funext j
      exact (ht j).trans (botFromSigns_affineSigns a b j).symm
    · have ha : a i ≠ 0 := by simpa [affineSigns, sign_eq_zero_iff] using hi
      refine ⟨affineRoot (a i) (b i), ?_⟩
      convert hroot using 1
      congr 1
      funext j
      exact (rootFromSigns_affineSigns a b ha j).symm
    · have ha : a i ≠ 0 := by simpa [affineSigns, sign_eq_zero_iff] using hi
      obtain ⟨t, ht⟩ := affine_right_sign_realized a b (affineRoot (a i) (b i))
      refine ⟨t, ?_⟩
      convert hright using 1
      congr 1
      funext j
      exact (ht j).trans (rightFromSigns_affineSigns a b ha j).symm

/-- The actual finite quantifier-free output formula. -/
def eliminateAffine [Fintype ι] [DecidableEq ι]
    (a b : ι → MvPolynomial κ ℝ) (φ : SignFormula ι) : PolynomialSignFormula κ :=
  (SignFormula.table (affineDecision φ)).map (affineAtoms a b)

/-- Correctness uses only signs of real-coefficient polynomials in the retained variables. -/
theorem eliminateAffine_correct [Fintype ι] [DecidableEq ι]
    (a b : ι → MvPolynomial κ ℝ) (φ : SignFormula ι) (x : κ → ℝ) :
    (eliminateAffine a b φ).realize x = true ↔
      ∃ t : ℝ, φ.eval (fun i => SignType.sign
        (MvPolynomial.eval x (a i) * t + MvPolynomial.eval x (b i))) = true := by
  have heq : (fun p => SignType.sign (MvPolynomial.eval x p)) ∘ affineAtoms a b =
      affineSigns (fun i => MvPolynomial.eval x (a i))
        (fun i => MvPolynomial.eval x (b i)) := by
    funext u
    rcases u with i | i | ⟨i, j⟩ <;> simp [affineAtoms, affineSigns, Function.comp_def]
  simp only [eliminateAffine, PolynomialSignFormula.realize, SignFormula.eval_map,
    SignFormula.eval_table, heq]
  exact (affineDecision_correct _ _ φ).symm

/-- Restricted projection closure, with an explicit finite output formula. -/
theorem isSemialgebraic_exists_affine [Fintype ι] [DecidableEq ι]
    (a b : ι → MvPolynomial κ ℝ) (φ : SignFormula ι) :
    IsSemialgebraic {x : κ → ℝ | ∃ t : ℝ, φ.eval (fun i => SignType.sign
      (MvPolynomial.eval x (a i) * t + MvPolynomial.eval x (b i))) = true} := by
  refine isSemialgebraic_iff_formula.mpr ⟨eliminateAffine a b φ, ?_⟩
  intro x
  exact (eliminateAffine_correct a b φ x).symm

end QuantumBehaviors.Projection
