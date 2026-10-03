import QuantumBehaviors.Projection.AffineElimination

/-!
# Finite guarded rational-expression compilation

Leaves contain numerator/denominator polynomials, and all branch guards are already
quantifier-free polynomial-sign formulas. Total real division is handled correctly even
when denominators vanish. Arithmetic and sign tests therefore stay in explicit finite
syntax; this is the target language for parameter-uniform coefficient algorithms.
-/

noncomputable section

namespace QuantumBehaviors.Projection

variable {ι : Type*}

inductive RationalTree (ι : Type*) where
  | leaf : MvPolynomial ι ℝ → MvPolynomial ι ℝ → RationalTree ι
  | branch : PolynomialSignFormula ι → RationalTree ι → RationalTree ι → RationalTree ι

def RationalTree.eval (x : ι → ℝ) : RationalTree ι → ℝ
  | .leaf n d => MvPolynomial.eval x n / MvPolynomial.eval x d
  | .branch φ t u => if φ.realize x then t.eval x else u.eval x

def RationalTree.bind (t : RationalTree ι)
    (f : MvPolynomial ι ℝ → MvPolynomial ι ℝ → RationalTree ι) : RationalTree ι :=
  match t with
  | .leaf n d => f n d
  | .branch φ t u => .branch φ (t.bind f) (u.bind f)

lemma RationalTree.eval_bind (t : RationalTree ι)
    (f : MvPolynomial ι ℝ → MvPolynomial ι ℝ → RationalTree ι)
    (g : ℝ → ℝ) (x : ι → ℝ)
    (hf : ∀ n d, (f n d).eval x = g (MvPolynomial.eval x n / MvPolynomial.eval x d)) :
    (t.bind f).eval x = g (t.eval x) := by
  induction t with
  | leaf n d => exact hf n d
  | branch φ t u ht hu => simp only [bind, eval]; split_ifs <;> assumption

/-- Zero guards are literal polynomial-sign atoms. -/
def zeroGuard (p : MvPolynomial ι ℝ) : PolynomialSignFormula ι := .atom p 0

@[simp] lemma zeroGuard_realize (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (zeroGuard p).realize x = true ↔ MvPolynomial.eval x p = 0 := by
  simp [zeroGuard, PolynomialSignFormula.realize, SignFormula.eval, sign_eq_zero_iff]

/-- Addition of two rational leaves, with the indispensable zero-denominator branches. -/
def rationalAddLeaf (a b c d : MvPolynomial ι ℝ) : RationalTree ι :=
  .branch (zeroGuard b) (.leaf c d)
    (.branch (zeroGuard d) (.leaf a b) (.leaf (a * d + c * b) (b * d)))

lemma rationalAddLeaf_eval (a b c d : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (rationalAddLeaf a b c d).eval x =
      MvPolynomial.eval x a / MvPolynomial.eval x b +
        MvPolynomial.eval x c / MvPolynomial.eval x d := by
  simp only [rationalAddLeaf, RationalTree.eval, zeroGuard_realize, map_add, map_mul]
  split_ifs with hb hd
  · simp [hb]
  · simp [hd]
  · simpa only [mul_comm] using (div_add_div (MvPolynomial.eval x a) (MvPolynomial.eval x c) hb hd).symm

def RationalTree.add (t u : RationalTree ι) : RationalTree ι :=
  t.bind fun a b => u.bind fun c d => rationalAddLeaf a b c d

def RationalTree.mul (t u : RationalTree ι) : RationalTree ι :=
  t.bind fun a b => u.bind fun c d => .leaf (a * c) (b * d)

def RationalTree.inv (t : RationalTree ι) : RationalTree ι :=
  t.bind fun a b => .leaf b a

def RationalTree.neg (t : RationalTree ι) : RationalTree ι :=
  t.bind fun a b => .leaf (-a) b

def RationalTree.ofPolynomial (p : MvPolynomial ι ℝ) : RationalTree ι := .leaf p 1

@[simp] theorem RationalTree.eval_ofPolynomial (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (RationalTree.ofPolynomial p).eval x = MvPolynomial.eval x p := by
  simp [ofPolynomial, eval]

@[simp] theorem RationalTree.eval_add (t u : RationalTree ι) (x : ι → ℝ) :
    (t.add u).eval x = t.eval x + u.eval x := by
  unfold add
  apply eval_bind t _ (fun r => r + u.eval x) x
  intro a b
  apply eval_bind u _ (fun s => MvPolynomial.eval x a / MvPolynomial.eval x b + s) x
  intro c d
  exact rationalAddLeaf_eval a b c d x

@[simp] theorem RationalTree.eval_mul (t u : RationalTree ι) (x : ι → ℝ) :
    (t.mul u).eval x = t.eval x * u.eval x := by
  unfold mul
  apply eval_bind t _ (fun r => r * u.eval x) x
  intro a b
  apply eval_bind u _ (fun s => MvPolynomial.eval x a / MvPolynomial.eval x b * s) x
  intro c d
  simp only [eval, map_mul, div_mul_div_comm]

@[simp] theorem RationalTree.eval_inv (t : RationalTree ι) (x : ι → ℝ) :
    t.inv.eval x = (t.eval x)⁻¹ := by
  unfold inv
  apply eval_bind t _ (fun r => r⁻¹) x
  intro a b
  simp only [eval, inv_div]

@[simp] theorem RationalTree.eval_neg (t : RationalTree ι) (x : ι → ℝ) :
    t.neg.eval x = -t.eval x := by
  unfold neg
  apply eval_bind t _ (fun r => -r) x
  intro a b
  simp only [eval, map_neg, neg_div]

/-- Compile any rational-expression sign test to finite polynomial-sign syntax. -/
def RationalTree.signFormula (s : SignType) : RationalTree ι → PolynomialSignFormula ι
  | .leaf n d => .atom (n * d) s
  | .branch φ t u => .disj (.conj φ (t.signFormula s)) (.conj (.neg φ) (u.signFormula s))

@[simp] theorem RationalTree.signFormula_correct (t : RationalTree ι) (s : SignType)
    (x : ι → ℝ) : (t.signFormula s).realize x = true ↔ SignType.sign (t.eval x) = s := by
  induction t with
  | leaf n d =>
      simp [signFormula, PolynomialSignFormula.realize, SignFormula.eval, eval,
        sign_div_real, sign_mul]
  | branch φ t u ht hu =>
      change ((φ.realize x && (t.signFormula s).realize x) ||
        (!(φ.realize x) && (u.signFormula s).realize x)) = true ↔ _
      simp only [Bool.or_eq_true, Bool.and_eq_true, ht, hu, Bool.not_eq_true', eval]
      cases hφ : φ.realize x <;> simp [hφ]

/-- Every rational-tree sign condition has the original genuine semialgebraic description. -/
theorem RationalTree.isSemialgebraic_sign (t : RationalTree ι) (s : SignType) :
    IsSemialgebraic {x : ι → ℝ | SignType.sign (t.eval x) = s} := by
  refine isSemialgebraic_iff_formula.mpr ⟨t.signFormula s, ?_⟩
  intro x
  exact (t.signFormula_correct s x).symm

end QuantumBehaviors.Projection
