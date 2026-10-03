import QuantumBehaviors.POVM.DilationEntries

/-! Separate local two-dimensional ancillas preserve cross-party commutation. -/
namespace QuantumBehaviors.POVM
open Matrix
open scoped BigOperators
variable {A : Type*} [Ring A] [StarRing A]

abbrev Ancilla := Fin 2 × Fin 2

def onAlice (P : Matrix (Fin 2) (Fin 2) A) : Matrix Ancilla Ancilla A :=
  fun x y => if x.2=y.2 then P x.1 y.1 else 0

def onBob (P : Matrix (Fin 2) (Fin 2) A) : Matrix Ancilla Ancilla A :=
  fun x y => if x.1=y.1 then P x.2 y.2 else 0

@[simp] lemma onAlice_one : onAlice (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j <;> by_cases hkl : k=l <;> simp [onAlice,Matrix.one_apply,Prod.mk.injEq,hij,hkl]

@[simp] lemma onBob_one : onBob (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j <;> by_cases hkl : k=l <;> simp [onBob,Matrix.one_apply,Prod.mk.injEq,hij,hkl]

@[simp] lemma onAlice_mul (P Q : Matrix (Fin 2) (Fin 2) A) : onAlice (P*Q)=onAlice P*onAlice Q := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hkl : k=l <;>
    simp [onAlice,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,hkl]

@[simp] lemma onBob_mul (P Q : Matrix (Fin 2) (Fin 2) A) : onBob (P*Q)=onBob P*onBob Q := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j <;>
    simp [onBob,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,hij]

@[simp] lemma onAlice_sub (P Q : Matrix (Fin 2) (Fin 2) A) : onAlice (P-Q)=onAlice P-onAlice Q := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hkl : k=l <;> simp [onAlice,hkl]

@[simp] lemma onBob_sub (P Q : Matrix (Fin 2) (Fin 2) A) : onBob (P-Q)=onBob P-onBob Q := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j <;> simp [onBob,hij]

@[simp] lemma onAlice_star (P : Matrix (Fin 2) (Fin 2) A) : onAlice P.conjTranspose=(onAlice P).conjTranspose := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hkl : k=l
  · subst l; simp [onAlice,Matrix.conjTranspose_apply]
  · simp [onAlice,Matrix.conjTranspose_apply,hkl,Ne.symm hkl]

@[simp] lemma onBob_star (P : Matrix (Fin 2) (Fin 2) A) : onBob P.conjTranspose=(onBob P).conjTranspose := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j
  · subst j; simp [onBob,Matrix.conjTranspose_apply]
  · simp [onBob,Matrix.conjTranspose_apply,hij,Ne.symm hij]

lemma onAlice_projection {P : Matrix (Fin 2) (Fin 2) A} (hP : IsStarProjection P) : IsStarProjection (onAlice P) := by
  constructor
  · change onAlice P*onAlice P=onAlice P
    rw [← onAlice_mul,hP.isIdempotentElem.eq]
  · change (onAlice P).conjTranspose=onAlice P
    have hs : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    rw [← onAlice_star,hs]

lemma onBob_projection {P : Matrix (Fin 2) (Fin 2) A} (hP : IsStarProjection P) : IsStarProjection (onBob P) := by
  constructor
  · change onBob P*onBob P=onBob P
    rw [← onBob_mul,hP.isIdempotentElem.eq]
  · change (onBob P).conjTranspose=onBob P
    have hs : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    rw [← onBob_star,hs]

lemma onAlice_mul_onBob (P Q : Matrix (Fin 2) (Fin 2) A) (i k j l : Fin 2) :
    (onAlice P*onBob Q) (i,k) (j,l)=P i j*Q k l := by
  simp [Matrix.mul_apply,onAlice,onBob,Fintype.sum_prod_type,ite_mul,mul_ite]

lemma onBob_mul_onAlice (P Q : Matrix (Fin 2) (Fin 2) A) (i k j l : Fin 2) :
    (onBob Q*onAlice P) (i,k) (j,l)=Q k l*P i j := by
  simp [Matrix.mul_apply,onAlice,onBob,Fintype.sum_prod_type,ite_mul,mul_ite]

lemma separateAncillas_commute (P Q : Matrix (Fin 2) (Fin 2) A)
    (hPQ : ∀ i j k l, Commute (P i j) (Q k l)) : Commute (onAlice P) (onBob Q) := by
  change onAlice P*onBob Q=onBob Q*onAlice P
  ext ⟨i,k⟩ ⟨j,l⟩
  rw [onAlice_mul_onBob,onBob_mul_onAlice,(hPQ i j k l).eq]

end QuantumBehaviors.POVM
