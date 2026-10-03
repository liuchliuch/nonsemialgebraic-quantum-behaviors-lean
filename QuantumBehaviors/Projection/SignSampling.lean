import QuantumBehaviors.Projection.FiniteFormula
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Data.Finset.Max

/-!
# Nonlinear reduction to root-sign queries

A finite family of arbitrary real univariate polynomials is sampled by the roots of its
(nonzero-factor) product and of that product's derivative, together with the two eventual
sign vectors at infinity. This is the analytic sampling reduction. Uniform elimination
of the remaining root-sign queries is a separate algebraic obligation.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Set Polynomial
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- Drop identically zero factors without dropping the zero signs in the original family. -/
def rootProduct (p : ι → Polynomial ℝ) : Polynomial ℝ :=
  ∏ i, if p i = 0 then 1 else p i

lemma rootProduct_ne_zero (p : ι → Polynomial ℝ) : rootProduct p ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs with h
  · exact one_ne_zero
  · exact h

lemma rootProduct_eval_eq_zero (p : ι → Polynomial ℝ) (x : ℝ) :
    (rootProduct p).eval x = 0 ↔ ∃ i, p i ≠ 0 ∧ (p i).eval x = 0 := by
  classical
  simp only [rootProduct, eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hp : p i = 0
    · simp [hp] at hi
    · exact ⟨i, hp, by simpa [hp] using hi⟩
  · rintro ⟨i, hp, hi⟩
    exact ⟨i, by simpa [hp] using hi⟩

lemma polynomial_sign_const_on {p : Polynomial ℝ} {U : Set ℝ} (hU : IsPreconnected U)
    (hp : ∀ x ∈ U, p.eval x ≠ 0) {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  apply hU.constant (f := fun x => SignType.sign (p.eval x)) ?_ hx hy
  intro z hz
  exact ((continuousAt_sign_of_ne_zero (hp z hz)).comp
    (f := fun x => p.eval x) p.continuous.continuousAt).continuousWithinAt

lemma polynomial_family_sign_const_on (p : ι → Polynomial ℝ) {U : Set ℝ}
    (hU : IsPreconnected U) (hp : ∀ x ∈ U, (rootProduct p).eval x ≠ 0)
    {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) (i : ι) :
    SignType.sign ((p i).eval x) = SignType.sign ((p i).eval y) := by
  by_cases hi : p i = 0
  · simp [hi]
  apply polynomial_sign_const_on hU ?_ hx hy
  intro z hz heq
  exact hp z hz ((rootProduct_eval_eq_zero p z).mpr ⟨i, hi, heq⟩)

/-- Every finite polynomial sign vector has a root/critical-point or infinite-tail sample. -/
theorem polynomial_sign_sampling (p : ι → Polynomial ℝ) (t : ℝ) :
    (∀ᶠ x in atBot, ∀ i, SignType.sign ((p i).eval x) = SignType.sign ((p i).eval t)) ∨
    (∀ᶠ x in atTop, ∀ i, SignType.sign ((p i).eval x) = SignType.sign ((p i).eval t)) ∨
    ∃ x : ℝ, ((rootProduct p).eval x = 0 ∨ (rootProduct p).derivative.eval x = 0) ∧
      ∀ i, SignType.sign ((p i).eval x) = SignType.sign ((p i).eval t) := by
  classical
  let P := rootProduct p
  have hP : P ≠ 0 := rootProduct_ne_zero p
  by_cases ht : P.eval t = 0
  · exact Or.inr (Or.inr ⟨t, Or.inl ht, fun _ => rfl⟩)
  let leftRoots := P.roots.toFinset.filter (· < t)
  let rightRoots := P.roots.toFinset.filter (t < ·)
  by_cases hl : leftRoots.Nonempty
  · by_cases hr : rightRoots.Nonempty
    · obtain ⟨l, hlmem, hlmax⟩ := leftRoots.exists_max_image id hl
      obtain ⟨r, hrmem, hrmin⟩ := rightRoots.exists_min_image id hr
      have hlt : l < t := (Finset.mem_filter.mp hlmem).2
      have htr : t < r := (Finset.mem_filter.mp hrmem).2
      have hPl : P.eval l = 0 := (Polynomial.mem_roots hP).mp
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hlmem).1)
      have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hrmem).1)
      have hgap : ∀ x ∈ Ioo l r, P.eval x ≠ 0 := by
        intro x hx hzero
        have hxroot : x ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hP).mpr hzero)
        rcases lt_trichotomy x t with hxt | hxt | hxt
        · have hxl := hlmax x (Finset.mem_filter.mpr ⟨hxroot, hxt⟩)
          exact (not_le_of_gt hx.1) hxl
        · exact ht (hxt ▸ hzero)
        · have hrx := hrmin x (Finset.mem_filter.mpr ⟨hxroot, hxt⟩)
          exact (not_le_of_gt hx.2) hrx
      obtain ⟨x, hx, hxderiv⟩ := exists_deriv_eq_zero (lt_trans hlt htr)
        P.continuousOn (hPl.trans hPr.symm)
      refine Or.inr (Or.inr ⟨x, Or.inr ?_, ?_⟩)
      · simpa only [P.deriv] using hxderiv
      · exact polynomial_family_sign_const_on p isPreconnected_Ioo hgap hx ⟨hlt, htr⟩
    · apply Or.inr ∘ Or.inl
      filter_upwards [eventually_ge_atTop t] with x hx
      apply polynomial_family_sign_const_on p isPreconnected_Ici ?_ hx (by simp)
      intro z hz hzero
      have hzroot : z ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots hP).mpr hzero)
      change t ≤ z at hz
      rcases hz.eq_or_lt with h | h
      · exact ht (h.symm ▸ hzero)
      · exact hr ⟨z, Finset.mem_filter.mpr ⟨hzroot, h⟩⟩
  · apply Or.inl
    filter_upwards [eventually_le_atBot t] with x hx
    apply polynomial_family_sign_const_on p isPreconnected_Iic ?_ hx (by simp)
    intro z hz hzero
    have hzroot : z ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).mpr hzero)
    change z ≤ t at hz
    rcases hz.eq_or_lt with h | h
    · exact ht (h ▸ hzero)
    · exact hl ⟨z, Finset.mem_filter.mpr ⟨hzroot, h⟩⟩

end QuantumBehaviors.Projection
