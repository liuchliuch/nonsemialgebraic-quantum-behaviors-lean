import QuantumBehaviors.POVM.MatrixOperator
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing

/-! The two-by-two dilation over arbitrary bounded Hilbert-space operators. -/
namespace QuantumBehaviors.POVM
open Matrix
open scoped BigOperators ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def dilationEntries (E : H →L[ℂ] H) : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
  !![E, CFC.sqrt (E*(1-E)); CFC.sqrt (E*(1-E)),1-E]

theorem dilationEntries_projection (E : H →L[ℂ] H) (hE : 0 ≤ E) (hE0 : 0 ≤ 1-E) :
    IsStarProjection (dilationEntries E) := by
  let S := CFC.sqrt (E*(1-E))
  have hc : Commute E (1-E) := by change E*(1-E)=(1-E)*E;noncomm_ring
  have hpos : 0 ≤ E*(1-E) := hc.mul_nonneg hE hE0
  have hSS : S*S=E*(1-E) := CFC.sqrt_mul_sqrt_self _ hpos
  have hSEbase : Commute (E*(1-E)) E := by change E*(1-E)*E=E*(E*(1-E));noncomm_ring
  have hSE : S*E=E*S := (hSEbase.cfcₙ_nnreal NNReal.sqrt).eq
  have hS : star S=S := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hEs : star E=E := hE.isSelfAdjoint.star_eq
  constructor
  · change dilationEntries E*dilationEntries E=dilationEntries E
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply,Fin.sum_univ_two]
    · change E*E+S*S=E
      rw [hSS]
      noncomm_ring
    · change E*S+S*(1-E)=S
      noncomm_ring [hSE]
    · change S*E+(1-E)*S=S
      noncomm_ring [hSE]
    · change S*S+(1-E)*(1-E)=1-E
      rw [hSS]
      noncomm_ring
  · change (dilationEntries E).conjTranspose=dilationEntries E
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact hEs
    · exact hS
    · exact hS
    · exact hE0.isSelfAdjoint.star_eq

lemma commute_one_sub_left {A : Type*} [Ring A] {E F : A} (h : Commute E F) : Commute (1-E) F := by
  change (1-E)*F=F*(1-E)
  noncomm_ring [h.eq]

lemma commute_one_sub_right {A : Type*} [Ring A] {E F : A} (h : Commute E F) : Commute E (1-F) := by
  exact (commute_one_sub_left h.symm).symm

lemma dilationEntries_commute {E F : H →L[ℂ] H} (hEF : Commute E F) (i j k l : Fin 2) :
    Commute (dilationEntries E i j) (dilationEntries F k l) := by
  have hep : Commute E (F*(1-F)) := hEF.mul_right (commute_one_sub_right hEF)
  have hpe : Commute (E*(1-E)) F := hEF.mul_left (commute_one_sub_left hEF)
  have hpol : Commute (E*(1-E)) (F*(1-F)) := hpe.mul_right (commute_one_sub_right hpe)
  have hEFs : Commute E (CFC.sqrt (F*(1-F))) := (hep.symm.cfcₙ_nnreal NNReal.sqrt).symm
  have hEsF : Commute (CFC.sqrt (E*(1-E))) F := hpe.cfcₙ_nnreal NNReal.sqrt
  have hss : Commute (CFC.sqrt (E*(1-E))) (CFC.sqrt (F*(1-F))) :=
    ((hpol.cfcₙ_nnreal NNReal.sqrt).symm.cfcₙ_nnreal NNReal.sqrt).symm
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [dilationEntries,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  all_goals first | exact hEF | exact hEFs | exact hEsF | exact hss |
    exact commute_one_sub_left hEF | exact commute_one_sub_right hEF |
    exact commute_one_sub_right (commute_one_sub_left hEF) |
    exact commute_one_sub_left hEFs | exact commute_one_sub_right hEsF

end QuantumBehaviors.POVM
