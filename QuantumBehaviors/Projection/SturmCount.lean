import QuantumBehaviors.Projection.RemainderChain
import QuantumBehaviors.Projection.Vendored.SturmTheorem
import Mathlib.FieldTheory.Separable

/-!
# A constructed Sturm root counter

The signed Euclidean chain is proved to satisfy all Sturm conditions for separable real
polynomials. Thus its coefficient signs, rather than a supplied chain hypothesis, count
roots. This is an unweighted root counter, not yet the weighted Sturm–Tarski query theorem.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Polynomial
open scoped Topology

lemma simple_root_flanks {p : Polynomial ℝ} {r : ℝ} (hr : p.eval r = 0)
    (hd : p.derivative.eval r ≠ 0) :
    (∀ᶠ x in 𝓝[<] r, (p * p.derivative).eval x < 0) ∧
    (∀ᶠ x in 𝓝[>] r, 0 < (p * p.derivative).eval x) := by
  obtain ⟨s, hs⟩ := (Polynomial.dvd_iff_isRoot.mpr hr : X - C r ∣ p)
  have hsderiv : p.derivative.eval r = s.eval r := by
    rw [hs]
    simp [derivative_mul]
  have hpos : 0 < s.eval r * p.derivative.eval r := by
    rw [← hsderiv]
    exact mul_self_pos.mpr hd
  have hc : ContinuousAt (fun x : ℝ => s.eval x * p.derivative.eval x) r := by fun_prop
  have hevent : ∀ᶠ x in 𝓝 r, 0 < s.eval x * p.derivative.eval x :=
    hc.tendsto.eventually (eventually_gt_nhds hpos)
  have heq (x : ℝ) : (p * p.derivative).eval x =
      (x - r) * (s.eval x * p.derivative.eval x) := by
    have hpx : p.eval x = (x - r) * s.eval x := by
      rw [hs]
      simp
    rw [eval_mul, hpx]
    ring
  constructor
  · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxr
    rw [heq]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hxr) hx
  · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxr
    rw [heq]
    exact mul_pos (sub_pos.mpr hxr) hx

lemma noCommonRealRoot_derivative {p : Polynomial ℝ} (hp : p.Separable) :
    NoCommonRealRoot p p.derivative := by
  intro r hr
  exact hp.eval₂_derivative_ne_zero (RingHom.id ℝ) hr

/-- The constructed remainder chain is a genuine Sturm chain, with every condition proved. -/
theorem signedRemChain_isSturmChain {p : Polynomial ℝ} (hp : p ≠ 0) (hsep : p.Separable) :
    Sturm.IsSturmChain p (signedRemChain p p.derivative) where
  head := signedRemChain_head _ _
  root_flank := by
    intro r hr
    have hd : p.derivative.eval r ≠ 0 := noCommonRealRoot_derivative hsep r hr
    have hdn : p.derivative ≠ 0 := fun h => hd (by simp [h])
    refine ⟨p.derivative, ?_, hd, simple_root_flanks hr hd⟩
    simp only [signedRemChain_of_ne_zero p hdn, List.getElem?_cons_succ,
      signedRemChain_get_zero]
  nonzero_mem := signedRemChain_nonzero hp
  interior_alternates := signedRemChain_interior hp (noCommonRealRoot_derivative hsep)
  last_no_root := signedRemChain_last hp (noCommonRealRoot_derivative hsep)

/-- Exact real-root count from the leading coefficient signs of a terminating explicit chain. -/
theorem signedRemChain_count_roots {p : Polynomial ℝ} (hp : p ≠ 0) (hsep : p.Separable) :
    Sturm.sturmVarPosInf (signedRemChain p p.derivative) + p.roots.card =
      Sturm.sturmVarNegInf (signedRemChain p p.derivative) :=
  (signedRemChain_isSturmChain hp hsep).sturm (Polynomial.nodup_roots hsep)

end QuantumBehaviors.Projection
