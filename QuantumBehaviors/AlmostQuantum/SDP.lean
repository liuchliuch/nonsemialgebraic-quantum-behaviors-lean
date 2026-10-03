import QuantumBehaviors.AlmostQuantum.Reconstruction
import QuantumBehaviors.FiniteAffine

/-! The actual almost-quantum event certificate is one finite affine complex SDP. -/
namespace QuantumBehaviors.AlmostQuantum
open Matrix
open scoped BigOperators ComplexOrder

abbrev Auxiliary := Event × Event × Bool
abbrev Variable := Coordinate ⊕ Auxiliary
noncomputable local instance : DecidableEq Variable := Classical.decEq _
abbrev AffineComplex := Bool → AffineScalar Variable
abbrev Constraint := Unit ⊕ (Input × Option Input) ⊕ (Input × Option Input × Input) ⊕
  (Input × Option Input) ⊕ (Input × Option Input × Input) ⊕ Coordinate

def decodeGram (z : Auxiliary → ℝ) : Matrix Event Event ℂ := fun e f => ⟨z (e,f,false),z (e,f,true)⟩
noncomputable def affineEval (a : AffineComplex) (x : Variable → ℝ) : ℂ := ⟨(a false).eval x,(a true).eval x⟩
def affineConst (z : ℂ) : AffineComplex := fun b => AffineScalar.const (if b then z.im else z.re)
noncomputable def gramAffine (e f : Event) : AffineComplex := fun b => AffineScalar.coord (Sum.inr (e,f,b))
noncomputable def probabilityAffine (c : Coordinate) : AffineComplex :=
  fun b => if b then AffineScalar.const 0 else AffineScalar.coord (Sum.inl c)
def affineAdd (a b : AffineComplex) : AffineComplex := fun c => AffineScalar.add (a c) (b c)
def affineSub (a b : AffineComplex) : AffineComplex := fun c => AffineScalar.sub (a c) (b c)

@[simp] lemma affineEval_const (z : ℂ) (x : Variable → ℝ) : affineEval (affineConst z) x=z := by
  apply Complex.ext <;> simp [affineEval,affineConst]
@[simp] lemma affineEval_gram (e f : Event) (p : Behavior) (z : Auxiliary → ℝ) :
    affineEval (gramAffine e f) (Sum.elim p z)=decodeGram z e f := by
  apply Complex.ext <;> simp [affineEval,gramAffine,decodeGram]
@[simp] lemma affineEval_probability (c : Coordinate) (p : Behavior) (z : Auxiliary → ℝ) :
    affineEval (probabilityAffine c) (Sum.elim p z)=(p c : ℂ) := by
  apply Complex.ext <;> simp [affineEval,probabilityAffine]
@[simp] lemma affineEval_add (a b : AffineComplex) (x : Variable → ℝ) :
    affineEval (affineAdd a b) x=affineEval a x+affineEval b x := by
  apply Complex.ext <;> simp [affineEval,affineAdd]
@[simp] lemma affineEval_sub (a b : AffineComplex) (x : Variable → ℝ) :
    affineEval (affineSub a b) x=affineEval a x-affineEval b x := by
  apply Complex.ext <;> simp [affineEval,affineSub]

noncomputable def bornAffine (i j : Input) (a b : Bool) : AffineComplex :=
  if a then if b then gramAffine emptyEvent (jointEvent i j)
    else affineSub (gramAffine emptyEvent (aliceEvent i)) (gramAffine emptyEvent (jointEvent i j))
  else if b then affineSub (gramAffine emptyEvent (bobEvent j)) (gramAffine emptyEvent (jointEvent i j))
    else affineAdd (affineSub (affineSub (affineConst 1) (gramAffine emptyEvent (aliceEvent i)))
      (gramAffine emptyEvent (bobEvent j))) (gramAffine emptyEvent (jointEvent i j))

@[simp] lemma eval_bornAffine (i j : Input) (a b : Bool) (p : Behavior) (z : Auxiliary → ℝ) :
    affineEval (bornAffine i j a b) (Sum.elim p z)=bornValue (decodeGram z) i j a b := by
  cases a <;> cases b <;> simp [bornAffine,bornValue]

noncomputable def residual (p : Behavior) (Γ : Matrix Event Event ℂ) : Constraint → ℂ :=
  Sum.elim (fun _ => Γ emptyEvent emptyEvent-1)
    (Sum.elim (fun c => Γ (aliceRow c.1 c.2) emptyEvent-Γ (aliceRow c.1 c.2) (aliceEvent c.1))
    (Sum.elim (fun c => Γ (aliceRow c.1 c.2.1) (bobEvent c.2.2)-Γ (aliceRow c.1 c.2.1) (jointEvent c.1 c.2.2))
    (Sum.elim (fun c => Γ (bobRow c.1 c.2) emptyEvent-Γ (bobRow c.1 c.2) (bobEvent c.1))
    (Sum.elim (fun c => Γ (bobRow c.1 c.2.1) (aliceEvent c.2.2)-Γ (bobRow c.1 c.2.1) (jointEvent c.2.2 c.1))
      (fun c => (p c : ℂ)-bornValue Γ c.1 c.2.1 c.2.2.1 c.2.2.2)))))

noncomputable def residualAffine : Constraint → AffineComplex :=
  Sum.elim (fun _ => affineSub (gramAffine emptyEvent emptyEvent) (affineConst 1))
    (Sum.elim (fun c => affineSub (gramAffine (aliceRow c.1 c.2) emptyEvent) (gramAffine (aliceRow c.1 c.2) (aliceEvent c.1)))
    (Sum.elim (fun c => affineSub (gramAffine (aliceRow c.1 c.2.1) (bobEvent c.2.2)) (gramAffine (aliceRow c.1 c.2.1) (jointEvent c.1 c.2.2)))
    (Sum.elim (fun c => affineSub (gramAffine (bobRow c.1 c.2) emptyEvent) (gramAffine (bobRow c.1 c.2) (bobEvent c.1)))
    (Sum.elim (fun c => affineSub (gramAffine (bobRow c.1 c.2.1) (aliceEvent c.2.2)) (gramAffine (bobRow c.1 c.2.1) (jointEvent c.2.2 c.1)))
      (fun c => affineSub (probabilityAffine c) (bornAffine c.1 c.2.1 c.2.2.1 c.2.2.2))))))

lemma eval_residualAffine (p : Behavior) (z : Auxiliary → ℝ) (c : Constraint) :
    affineEval (residualAffine c) (Sum.elim p z)=residual p (decodeGram z) c := by
  rcases c with c | (c | (c | (c | (c | c)))) <;> simp [residualAffine,residual]

lemma residual_zero_iff (p : Behavior) (Γ : Matrix Event Event ℂ) :
    (∀ c, residual p Γ c=0) ↔
      Γ emptyEvent emptyEvent=1 ∧
      (∀ i t, Γ (aliceRow i t) emptyEvent=Γ (aliceRow i t) (aliceEvent i)) ∧
      (∀ i t j, Γ (aliceRow i t) (bobEvent j)=Γ (aliceRow i t) (jointEvent i j)) ∧
      (∀ j t, Γ (bobRow j t) emptyEvent=Γ (bobRow j t) (bobEvent j)) ∧
      (∀ j t i, Γ (bobRow j t) (aliceEvent i)=Γ (bobRow j t) (jointEvent i j)) ∧
      ∀ i j a b, (p (i,j,a,b) : ℂ)=bornValue Γ i j a b := by
  simp [residual,Sum.forall,Prod.forall,sub_eq_zero]

lemma certificate_iff_affine (p : Behavior) : Nonempty (Certificate p) ↔
    ∃ z : Auxiliary → ℝ, (decodeGram z).PosSemidef ∧
      ∀ c : Constraint × Bool, (residualAffine c.1 c.2).eval (Sum.elim p z)=0 := by
  have hz (z : Auxiliary → ℝ) : (∀ c : Constraint × Bool, (residualAffine c.1 c.2).eval (Sum.elim p z)=0) ↔
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
    let z : Auxiliary → ℝ := fun x => if x.2.2 then (c.gram x.1 x.2.1).im else (c.gram x.1 x.2.1).re
    have hg : decodeGram z=c.gram := by ext i j <;> rfl
    refine ⟨z,by rw [hg];exact c.positive,(hz z).mpr ?_⟩
    rw [hg,residual_zero_iff]
    exact ⟨c.normalized,c.alice_empty,c.alice_bob,c.bob_empty,c.bob_alice,c.born⟩
  · rintro ⟨z,hpos,heq⟩
    obtain ⟨hn,hA0,hAB,hB0,hBA,hp⟩ := (residual_zero_iff p (decodeGram z)).mp ((hz z).mp heq)
    exact ⟨⟨decodeGram z,hpos,hn,hA0,hAB,hB0,hBA,hp⟩⟩

noncomputable def gramMatrixAffine : ComplexAffineMatrix Variable (Fintype.card Event) :=
  fun c => AffineScalar.coord (Sum.inr ((Fintype.equivFin Event).symm c.1,
    (Fintype.equivFin Event).symm c.2.1,c.2.2))

lemma gramMatrixAffine_positive_iff (p : Behavior) (z : Auxiliary → ℝ) :
    (gramMatrixAffine.eval (Sum.elim p z)).PosSemidef ↔ (decodeGram z).PosSemidef := by
  let e : Fin (Fintype.card Event) ≃ Event := (Fintype.equivFin Event).symm
  have heq : gramMatrixAffine.eval (Sum.elim p z)=(decodeGram z).submatrix e e := by
    ext i j <;> simp [ComplexAffineMatrix.eval,gramMatrixAffine,complexMatrix,decodeGram,e]
  rw [heq]
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simpa only [Matrix.submatrix_submatrix,Equiv.self_comp_symm,Matrix.submatrix_id_id] using hh
  · exact fun h => h.submatrix e

/-- One 25×25 affine Hermitian positivity constraint plus finitely many affine real equalities. -/
theorem finite_complex_sdp : HasFiniteComplexSDPLift behaviors := by
  apply HasFiniteComplexSDPLift.of_finite gramMatrixAffine (fun c : Constraint × Bool => residualAffine c.1 c.2)
  intro p
  rw [mem_iff_certificate,certificate_iff_affine]
  simp_rw [gramMatrixAffine_positive_iff]

end QuantumBehaviors.AlmostQuantum
