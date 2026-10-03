import QuantumBehaviors.NPA.Models
import QuantumBehaviors.FiniteAffineMany

/-! Each genuine NPA level is an explicit finite collection of affine Hermitian LMIs. -/
namespace QuantumBehaviors.NPA
open Matrix
open scoped BigOperators ComplexOrder

abbrev Auxiliary (k : ℕ) := BoundedWord (k+1) × BoundedWord (k+1) × Bool
abbrev Variable (k : ℕ) := Coordinate ⊕ Auxiliary k
abbrev AffineComplex (k : ℕ) := Bool → AffineScalar (Variable k)
abbrev Constraint (k : ℕ) := Unit ⊕ (BoundedWord (k+1) × BoundedWord (k+1) × BoundedWord (k+1) × BoundedWord (k+1)) ⊕ Coordinate
abbrev LMIIndex := Unit ⊕ Coordinate
variable {k : ℕ}
noncomputable local instance : DecidableEq (Variable k) := Classical.decEq _
attribute [local instance] Classical.propDecidable

def decodeGram (z : Auxiliary k → ℝ) : Matrix (BoundedWord (k+1)) (BoundedWord (k+1)) ℂ := fun e f => ⟨z (e,f,false),z (e,f,true)⟩
noncomputable def affineEval (a : AffineComplex k) (x : Variable k → ℝ) : ℂ := ⟨(a false).eval x,(a true).eval x⟩
def affineConst (z : ℂ) : AffineComplex k := fun b => AffineScalar.const (if b then z.im else z.re)
noncomputable def gramAffine (e f : BoundedWord (k+1)) : AffineComplex k := fun b => AffineScalar.coord (Sum.inr (e,f,b))
noncomputable def probabilityAffine (c : Coordinate) : AffineComplex k := fun b => if b then AffineScalar.const 0 else AffineScalar.coord (Sum.inl c)
def affineAdd (a b : AffineComplex k) : AffineComplex k := fun c => AffineScalar.add (a c) (b c)
def affineSub (a b : AffineComplex k) : AffineComplex k := fun c => AffineScalar.sub (a c) (b c)

@[simp] lemma affineEval_const (z : ℂ) (x : Variable k → ℝ) : affineEval (affineConst z) x=z := by
  apply Complex.ext <;> simp [affineEval,affineConst]
@[simp] lemma affineEval_gram (e f : BoundedWord (k+1)) (p : Behavior) (z : Auxiliary k → ℝ) :
    affineEval (gramAffine e f) (Sum.elim p z)=decodeGram z e f := by
  apply Complex.ext <;> simp [affineEval,gramAffine,decodeGram]
@[simp] lemma affineEval_probability (c : Coordinate) (p : Behavior) (z : Auxiliary k → ℝ) :
    affineEval (probabilityAffine c) (Sum.elim p z)=(p c : ℂ) := by
  apply Complex.ext <;> simp [affineEval,probabilityAffine]
@[simp] lemma affineEval_add (a b : AffineComplex k) (x : Variable k → ℝ) :
    affineEval (affineAdd a b) x=affineEval a x+affineEval b x := by
  apply Complex.ext <;> simp [affineEval,affineAdd]
@[simp] lemma affineEval_sub (a b : AffineComplex k) (x : Variable k → ℝ) :
    affineEval (affineSub a b) x=affineEval a x-affineEval b x := by
  apply Complex.ext <;> simp [affineEval,affineSub]

noncomputable def bornAffine (k : ℕ) (i j : Input) (a b : Bool) : AffineComplex k :=
  let α := gramAffine (emptyIndex k) (letterIndex k (Sum.inl i))
  let β := gramAffine (emptyIndex k) (letterIndex k (Sum.inr j))
  let γ := gramAffine (letterIndex k (Sum.inl i)) (letterIndex k (Sum.inr j))
  if a then if b then γ else affineSub α γ else if b then affineSub β γ
    else affineAdd (affineSub (affineSub (affineConst 1) α) β) γ

@[simp] lemma eval_bornAffine (i j : Input) (a b : Bool) (p : Behavior) (z : Auxiliary k → ℝ) :
    affineEval (bornAffine k i j a b) (Sum.elim p z)=bornValue k (decodeGram z) i j a b := by
  cases a <;> cases b <;> simp [bornAffine,bornValue]

noncomputable def residual (p : Behavior) (Γ : Matrix (BoundedWord (k+1)) (BoundedWord (k+1)) ℂ) : Constraint k → ℂ :=
  Sum.elim (fun _ => Γ (emptyIndex k) (emptyIndex k)-1)
    (Sum.elim (fun c => if WordRel (c.1.val.reverse++c.2.1.val) (c.2.2.1.val.reverse++c.2.2.2.val)
      then Γ c.1 c.2.1-Γ c.2.2.1 c.2.2.2 else 0)
      (fun c => (p c : ℂ)-bornValue k Γ c.1 c.2.1 c.2.2.1 c.2.2.2))

noncomputable def residualAffine (k : ℕ) : Constraint k → AffineComplex k :=
  Sum.elim (fun _ => affineSub (gramAffine (emptyIndex k) (emptyIndex k)) (affineConst 1))
    (Sum.elim (fun c => if WordRel (c.1.val.reverse++c.2.1.val) (c.2.2.1.val.reverse++c.2.2.2.val)
      then affineSub (gramAffine c.1 c.2.1) (gramAffine c.2.2.1 c.2.2.2) else affineConst 0)
      (fun c => affineSub (probabilityAffine c) (bornAffine k c.1 c.2.1 c.2.2.1 c.2.2.2)))

lemma eval_residualAffine (p : Behavior) (z : Auxiliary k → ℝ) (c : Constraint k) :
    affineEval (residualAffine k c) (Sum.elim p z)=residual p (decodeGram z) c := by
  rcases c with c | (c | c)
  · simp [residualAffine,residual]
  · dsimp only [residualAffine,residual,Sum.elim_inr,Sum.elim_inl]
    split_ifs <;> simp
  · simp [residualAffine,residual]

lemma residual_zero_iff (p : Behavior) (Γ : Matrix (BoundedWord (k+1)) (BoundedWord (k+1)) ℂ) :
    (∀ c, residual p Γ c=0) ↔
      Γ (emptyIndex k) (emptyIndex k)=1 ∧
      (∀ u v r s, WordRel (u.val.reverse++v.val) (r.val.reverse++s.val) → Γ u v=Γ r s) ∧
      ∀ i j a b, (p (i,j,a,b) : ℂ)=bornValue k Γ i j a b := by
  simp [residual,Sum.forall,Prod.forall,sub_eq_zero]

lemma certificate_iff_affine (p : Behavior) : Nonempty (Certificate k p) ↔
    ∃ z : Auxiliary k → ℝ, ((decodeGram z).PosSemidef ∧ Nonnegative p) ∧
      ∀ c : Constraint k × Bool, (residualAffine k c.1 c.2).eval (Sum.elim p z)=0 := by
  have hz (z : Auxiliary k → ℝ) : (∀ c : Constraint k × Bool, (residualAffine k c.1 c.2).eval (Sum.elim p z)=0) ↔
      ∀ c, residual p (decodeGram z) c=0 := by
    simp only [← eval_residualAffine,affineEval,Complex.ext_iff,Complex.zero_re,Complex.zero_im]
    constructor
    · intro h c
      exact ⟨h (c,false),h (c,true)⟩
    · intro h c
      rcases c with ⟨c,b⟩
      cases b
      · exact (h c).1
      · exact (h c).2
  constructor
  · rintro ⟨c⟩
    let z : Auxiliary k → ℝ := fun x => if x.2.2 then (c.gram x.1 x.2.1).im else (c.gram x.1 x.2.1).re
    have hg : decodeGram z=c.gram := by ext i j <;> rfl
    refine ⟨z,⟨by rw [hg];exact c.positive,c.nonnegative⟩,(hz z).mpr ?_⟩
    rw [hg,residual_zero_iff]
    exact ⟨c.normalized,c.relations,c.born⟩
  · rintro ⟨z,⟨hpos,hnn⟩,heq⟩
    obtain ⟨hn,hrel,hp⟩ := (residual_zero_iff p (decodeGram z)).mp ((hz z).mp heq)
    exact ⟨⟨decodeGram z,hpos,hn,hrel,hp,hnn⟩⟩

noncomputable def gramMatrixAffine (k : ℕ) : ComplexAffineMatrix (Variable k) (Fintype.card (BoundedWord (k+1))) :=
  fun c => AffineScalar.coord (Sum.inr ((Fintype.equivFin (BoundedWord (k+1))).symm c.1,
    (Fintype.equivFin (BoundedWord (k+1))).symm c.2.1,c.2.2))

lemma gramMatrixAffine_positive_iff (p : Behavior) (z : Auxiliary k → ℝ) :
    ((gramMatrixAffine k).eval (Sum.elim p z)).PosSemidef ↔ (decodeGram z).PosSemidef := by
  let e : Fin (Fintype.card (BoundedWord (k+1))) ≃ BoundedWord (k+1) := (Fintype.equivFin _).symm
  have heq : (gramMatrixAffine k).eval (Sum.elim p z)=(decodeGram z).submatrix e e := by
    ext i j <;> simp [ComplexAffineMatrix.eval,gramMatrixAffine,complexMatrix,decodeGram,e]
  rw [heq]
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simpa only [Matrix.submatrix_submatrix,Equiv.self_comp_symm,Matrix.submatrix_id_id] using hh
  · exact fun h => h.submatrix e

noncomputable def lmiSize (k : ℕ) : LMIIndex → ℕ := Sum.elim (fun _ => Fintype.card (BoundedWord (k+1))) (fun _ => 1)
noncomputable def lmiData (k : ℕ) : ∀ q : LMIIndex, ComplexAffineMatrix (Variable k) (lmiSize k q)
  | Sum.inl _ => gramMatrixAffine k
  | Sum.inr x => fun c => if c.2.2 then AffineScalar.const 0 else AffineScalar.coord (Sum.inl x)

lemma scalar_psd_iff (r : ℝ) : Matrix.PosSemidef (fun _ _ : Fin 1 => (r : ℂ)) ↔ 0 ≤ r := by
  constructor
  · intro h
    exact (RCLike.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
  · intro h
    have hc : 0 ≤ (r : ℂ) := by simpa using h
    have hp := Matrix.PosSemidef.diagonal (fun _ : Fin 1 => hc)
    convert hp using 1
    ext i j
    simp [Matrix.diagonal_apply,Subsingleton.elim i j]

lemma lmi_probability_eval (p : Behavior) (z : Auxiliary k → ℝ) (x : Coordinate) :
    (lmiData k (Sum.inr x)).eval (Sum.elim p z)=fun _ _ : Fin 1 => (p x : ℂ) := by
  apply Matrix.ext
  intro i j
  apply Complex.ext <;> simp [lmiData,ComplexAffineMatrix.eval,complexMatrix]

lemma all_lmi_positive_iff (p : Behavior) (z : Auxiliary k → ℝ) :
    (∀ q, ((lmiData k q).eval (Sum.elim p z)).PosSemidef) ↔ (decodeGram z).PosSemidef ∧ Nonnegative p := by
  constructor
  · intro h
    refine ⟨(gramMatrixAffine_positive_iff p z).mp (h (Sum.inl ())),?_⟩
    intro x
    have hx := h (Sum.inr x)
    rwa [lmi_probability_eval,scalar_psd_iff] at hx
  · rintro ⟨hΓ,hp⟩ q
    cases q with
    | inl u => exact (gramMatrixAffine_positive_iff p z).mpr hΓ
    | inr x => rw [lmi_probability_eval,scalar_psd_iff];exact hp x

/-- Genuine finite NPA feasibility, including positivity of all observed probabilities. -/
theorem finite_complex_sdp (k : ℕ) : HasFiniteComplexSDPLift (level k) := by
  apply HasFiniteComplexSDPLift.of_finiteMany (lmiSize k) (lmiData k)
    (fun c : Constraint k × Bool => residualAffine k c.1 c.2)
  intro p
  change Nonempty (Certificate k p) ↔ _
  rw [certificate_iff_affine]
  simp_rw [all_lmi_positive_iff]

end QuantumBehaviors.NPA
