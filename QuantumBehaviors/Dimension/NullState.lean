import QuantumBehaviors.StateGNS
import Mathlib.Tactic.NoncommRing

/-!
# Zero-probability rigidity on the support of a density matrix

These lemmas keep the original matrix dimensions. They do not use the doubled POVM dilation,
which would be inadequate for the sharp local-dimension lower bounds in S14.
-/
namespace QuantumBehaviors.Dimension

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma trace_product_nonnegative {ρ X : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (ρ * X).trace := (densityFunctional ρ hρ).map_nonneg hX.nonneg

lemma complex_eq_zero_of_nonneg_of_re_eq_zero {z : ℂ} (hz : 0 ≤ z) (hr : z.re = 0) : z = 0 := by
  apply Complex.ext
  · exact hr
  · exact (RCLike.nonneg_iff.mp hz).2

lemma density_square_trace (ρ X : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    ((X * CFC.sqrt ρ).conjTranspose * (X * CFC.sqrt ρ)).trace = (ρ * (X.conjTranspose * X)).trace := by
  let S := CFC.sqrt ρ
  have hS : S.conjTranspose = S := (CFC.sqrt_nonneg ρ).isSelfAdjoint
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  change ((X * S).conjTranspose * (X * S)).trace = _
  rw [Matrix.conjTranspose_mul, hS]
  calc
    _ = (S * ((X.conjTranspose * X) * S)).trace := by congr 1; noncomm_ring
    _ = (((X.conjTranspose * X) * S) * S).trace := Matrix.trace_mul_comm _ _
    _ = ((X.conjTranspose * X) * ρ).trace := by rw [Matrix.mul_assoc, hSS]
    _ = _ := Matrix.trace_mul_comm _ _

lemma density_square_zero {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (X : Matrix ι ι ℂ)
    (hzero : (ρ * (X.conjTranspose * X)).trace = 0) : X * CFC.sqrt ρ = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [density_square_trace ρ X hρ, hzero]

lemma density_positive_zero {ρ X : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hX : X.PosSemidef)
    (hzero : (ρ * X).trace = 0) : X * CFC.sqrt ρ = 0 := by
  let S := CFC.sqrt X
  have hS : S.conjTranspose = S := (CFC.sqrt_nonneg X).isSelfAdjoint
  have hSS : S * S = X := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have hs : S * CFC.sqrt ρ = 0 := density_square_zero hρ S (by simpa [hS, hSS] using hzero)
  rw [← hSS, Matrix.mul_assoc, hs, mul_zero]

lemma effect_variance_positive {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (hX0 : (1 - X).PosSemidef) :
    (X - X * X).PosSemidef := by
  have hcomm : Commute X (1 - X) := by change X * (1 - X) = (1 - X) * X; noncomm_ring
  have h : 0 ≤ X * (1 - X) := Commute.mul_nonneg hX.nonneg hX0.nonneg hcomm
  simpa only [mul_sub, mul_one] using h.posSemidef

lemma mismatch_decomposition {X Y : Matrix ι ι ℂ} (hX : X.conjTranspose = X)
    (hY : Y.conjTranspose = Y) (hXY : Commute X Y) :
    X * (1 - Y) + (1 - X) * Y =
      (X - Y).conjTranspose * (X - Y) + (X - X * X) + (Y - Y * Y) := by
  rw [Matrix.conjTranspose_sub, hX, hY]
  noncomm_ring [hXY.eq]

/-- Synchrony forces equality and idempotence on the original density support. -/
theorem synchronous_effect_support {ρ X Y : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hX : X.PosSemidef) (hX0 : (1 - X).PosSemidef)
    (hY : Y.PosSemidef) (hY0 : (1 - Y).PosSemidef) (hXY : Commute X Y)
    (hzero : (ρ * (X * (1 - Y) + (1 - X) * Y)).trace = 0) :
    (X - Y) * CFC.sqrt ρ = 0 ∧ (X - X * X) * CFC.sqrt ρ = 0 ∧
      (Y - Y * Y) * CFC.sqrt ρ = 0 := by
  let D := (X - Y).conjTranspose * (X - Y)
  let U := X - X * X
  let V := Y - Y * Y
  have hD : D.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hU : U.PosSemidef := effect_variance_positive hX hX0
  have hV : V.PosSemidef := effect_variance_positive hY hY0
  have hdecomp := mismatch_decomposition hX.isHermitian.eq hY.isHermitian.eq hXY
  have hsum : (ρ * D).trace + (ρ * U).trace + (ρ * V).trace = 0 := by
    rw [hdecomp, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add] at hzero
    exact hzero
  have hDn := trace_product_nonnegative hρ hD
  have hUn := trace_product_nonnegative hρ hU
  have hVn := trace_product_nonnegative hρ hV
  have hDr : 0 ≤ (ρ * D).trace.re := (RCLike.nonneg_iff.mp hDn).1
  have hUr : 0 ≤ (ρ * U).trace.re := (RCLike.nonneg_iff.mp hUn).1
  have hVr : 0 ≤ (ρ * V).trace.re := (RCLike.nonneg_iff.mp hVn).1
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.zero_re] at hre
  have hDz := complex_eq_zero_of_nonneg_of_re_eq_zero hDn (by linarith)
  have hUz := complex_eq_zero_of_nonneg_of_re_eq_zero hUn (by linarith)
  have hVz := complex_eq_zero_of_nonneg_of_re_eq_zero hVn (by linarith)
  exact ⟨density_square_zero hρ (X - Y) hDz,
    density_positive_zero hρ hU hUz, density_positive_zero hρ hV hVz⟩

end QuantumBehaviors.Dimension
