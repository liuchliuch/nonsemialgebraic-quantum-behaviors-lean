import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Algebraic spectral reflection for two idempotents

The reflection of the spectrum of a sum of two projections is algebraic.  The
proof constructs a resolvent at `z` from a resolvent at `2 - z`; consequently it
works in arbitrary field algebras, without finite-dimensionality or an
approximate-eigenvector argument.
-/

namespace QuantumBehaviors

section Ring

variable {A : Type*} [Ring A]

/-- A two-sided resolvent-transfer identity. -/
lemma isUnit_of_reflection_identities {x y d c : A}
    (hxy : x * y = y * x)
    (hsum : x * y + d * d = c)
    (hxd : x * d = -(d * y))
    (hdx : d * x = -(y * d))
    (hc : IsUnit c) (hy : IsUnit y) : IsUnit x := by
  obtain ⟨r, hyr, hry⟩ := isUnit_iff_exists.mp hy
  have hl : x * (y - d * r * d) = c := by
    calc
      x * (y - d * r * d) = x * y - (x * d) * r * d := by noncomm_ring
      _ = x * y + d * (y * r) * d := by rw [hxd]; noncomm_ring
      _ = c := by simpa only [hyr, mul_one] using hsum
  have hr : (y - d * r * d) * x = c := by
    calc
      (y - d * r * d) * x = y * x - d * r * (d * x) := by noncomm_ring
      _ = y * x + d * (r * y) * d := by rw [hdx]; noncomm_ring
      _ = c := by simpa only [hry, mul_one, ← hxy] using hsum
  have hcomm : Commute x (y - d * r * d) := hl.trans hr.symm
  exact (hcomm.isUnit_mul_iff.mp (hl.symm ▸ hc)).1

end Ring

section Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The spectrum of the sum of two idempotents is reflected about `1`, except
possibly at the endpoints `0` and `2`.  Self-adjointness is not needed. -/
theorem spectral_reflection {P Q : A}
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    {z : K} (hz₀ : z ≠ 0) (hz₂ : z ≠ 2)
    (hz : z ∈ spectrum K (P + Q)) : 2 - z ∈ spectrum K (P + Q) := by
  by_contra hnot
  have hy : IsUnit (2 - algebraMap K A z - (P + Q)) := by
    simpa only [map_sub, map_ofNat] using spectrum.notMem_iff.mp hnot
  have hc : IsUnit (algebraMap K A z * (2 - algebraMap K A z)) := by
    have hscalar : IsUnit (z * (2 - z)) :=
      isUnit_iff_ne_zero.mpr (mul_ne_zero hz₀ (sub_ne_zero.mpr (Ne.symm hz₂)))
    simpa only [map_mul, map_sub, map_ofNat] using hscalar.map (algebraMap K A)
  have hrP := (Algebra.commutes (R := K) (A := A) z P)
  have hrQ := (Algebra.commutes (R := K) (A := A) z Q)
  apply spectrum.mem_iff.mp hz
  apply isUnit_of_reflection_identities
    (y := 2 - algebraMap K A z - (P + Q)) (d := P - Q)
    (c := algebraMap K A z * (2 - algebraMap K A z))
  · noncomm_ring [hrP, hrQ]
  · noncomm_ring [hP.eq, hQ.eq, hrP, hrQ]
  · noncomm_ring [hP.eq, hQ.eq, hrP, hrQ]
  · noncomm_ring [hP.eq, hQ.eq, hrP, hrQ]
  · exact hc
  · exact hy

/-- Reflection of real spectral points, in the open interval needed for the
four-projection classification. -/
theorem spectral_reflection_real {A : Type*} [Ring A] [Algebra ℝ A]
    {P Q : A} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    {z : ℝ} (hz₀ : 0 < z) (hz₂ : z < 2)
    (hz : z ∈ spectrum ℝ (P + Q)) : 2 - z ∈ spectrum ℝ (P + Q) :=
  spectral_reflection hP hQ hz₀.ne' hz₂.ne hz

/-- The affine spectral map needed below, proved directly from the definition
of spectrum rather than requiring a polynomial spectral-mapping theorem. -/
theorem spectrum_scalar_sub_iff {A : Type*} [Ring A] [Algebra ℝ A]
    (a : A) (α z : ℝ) :
    α - z ∈ spectrum ℝ (algebraMap ℝ A α - a) ↔ z ∈ spectrum ℝ a := by
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have h : algebraMap ℝ A (α - z) - (algebraMap ℝ A α - a) =
      -(algebraMap ℝ A z - a) := by rw [map_sub]; noncomm_ring
  rw [h, IsUnit.neg_iff]

end Algebra

end QuantumBehaviors
