import QuantumBehaviors.NPA.Models
import QuantumBehaviors.ComplexSemidefinite
import QuantumBehaviors.Scenarios.CompactMatrixFacts

/-! Actual finite Hilbert Gram vectors and the bounded-entry lemma for NPA certificates. -/
namespace QuantumBehaviors.NPA
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {J : Type*} [Fintype J] [DecidableEq J]
noncomputable def gramVector (Γ : Matrix J J ℂ) (j : J) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun i => CFC.sqrt Γ i j)

lemma gramVector_inner {Γ : Matrix J J ℂ} (hΓ : Γ.PosSemidef) (i j : J) :
    inner ℂ (gramVector Γ i) (gramVector Γ j)=Γ i j := by
  have hs : (CFC.sqrt Γ).conjTranspose=CFC.sqrt Γ := (CFC.sqrt_nonneg Γ).isSelfAdjoint
  have hsq : (CFC.sqrt Γ).conjTranspose*CFC.sqrt Γ=Γ := by rw [hs,CFC.sqrt_mul_sqrt_self Γ hΓ.nonneg]
  have he : inner ℂ (gramVector Γ i) (gramVector Γ j)=((CFC.sqrt Γ).conjTranspose*CFC.sqrt Γ) i j := by
    simp [gramVector,PiLp.inner_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm]
  rw [he,hsq]

lemma gramVector_norm_sq {Γ : Matrix J J ℂ} (hΓ : Γ.PosSemidef) (i : J) :
    ‖gramVector Γ i‖^2=(Γ i i).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),gramVector_inner hΓ]
  rfl

lemma gram_diagonal_le_of_repeat {Γ : Matrix J J ℂ} (hΓ : Γ.PosSemidef) (u v : J)
    (hrep : Γ v v=Γ v u) : (Γ v v).re ≤ (Γ u u).re := by
  let x := gramVector Γ u
  let y := gramVector Γ v
  have h1 : inner ℂ y y=inner ℂ y x := by simp only [x,y,gramVector_inner hΓ,hrep]
  have h2 : inner ℂ y y=inner ℂ x y := by
    have h := congrArg star h1
    simpa only [← starRingEnd_apply,inner_conj_symm] using h
  have hn : 0 ≤ (inner ℂ (x-y) (x-y)).re := inner_self_nonneg (𝕜 := ℂ) (x := x-y)
  rw [inner_sub_left,inner_sub_right,inner_sub_right,← h1,← h2] at hn
  simp only [Complex.sub_re,sub_self,sub_zero] at hn
  simpa only [x,y,gramVector_inner hΓ] using sub_nonneg.mp hn

lemma Certificate.diagonal_le_one {k : ℕ} {p : Behavior} (c : Certificate k p)
    (u : BoundedWord (k+1)) : (c.gram u u).re ≤ 1 := by
  have haux : ∀ w : Word, ∀ hw : w.length ≤ k+1,
      (c.gram ⟨w,hw⟩ ⟨w,hw⟩).re ≤ 1 := by
    intro w
    induction w with
    | nil =>
        intro hw
        change (c.gram (emptyIndex k) (emptyIndex k)).re ≤ 1
        rw [c.normalized]
        norm_num
    | cons a w ih =>
        intro hw
        have hwl : w.length ≤ k+1 := by simp only [List.length_cons] at hw;omega
        have hrep : c.gram ⟨a::w,hw⟩ ⟨a::w,hw⟩=c.gram ⟨a::w,hw⟩ ⟨w,hwl⟩ :=
          c.relations _ _ _ _ (WordRel.projection_inner a w w)
        exact (gram_diagonal_le_of_repeat c.positive ⟨w,hwl⟩ ⟨a::w,hw⟩ hrep).trans (ih hwl)
  exact haux u.val u.property

lemma Certificate.entry_norm_le_one {k : ℕ} {p : Behavior} (c : Certificate k p)
    (u v : BoundedWord (k+1)) : ‖c.gram u v‖ ≤ 1 :=
  Scenarios.psd_entry_norm_le_one c.positive c.diagonal_le_one u v

lemma Certificate.gramVector_norm_le_one {k : ℕ} {p : Behavior} (c : Certificate k p)
    (u : BoundedWord (k+1)) : ‖gramVector c.gram u‖ ≤ 1 := by
  have hsq := gramVector_norm_sq c.positive u
  have hle := c.diagonal_le_one u
  nlinarith [norm_nonneg (gramVector c.gram u)]

end QuantumBehaviors.NPA
