import QuantumBehaviors.Projection.AffineSampling
import QuantumBehaviors.Projection.Vendored.SturmChainDefs
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Signed Euclidean remainder chains

This is an actual terminating chain construction, not an assumed Sturm certificate.
The signs of its endpoint coefficients will later be made uniform in polynomial parameters.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Polynomial

/-- Consecutive polynomials have no simultaneous real zero. -/
def NoCommonRealRoot (p q : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, p.eval x = 0 → q.eval x ≠ 0

lemma eval_mod_of_eval_eq_zero (p : Polynomial ℝ) {q : Polynomial ℝ} {x : ℝ}
    (hq : q.eval x = 0) : (p % q).eval x = p.eval x := by
  have h := congrArg (Polynomial.eval x) (EuclideanDomain.mod_add_div p q)
  simpa [hq] using h

lemma NoCommonRealRoot.remainder {p q : Polynomial ℝ} (h : NoCommonRealRoot p q) :
    NoCommonRealRoot q (-(p % q)) := by
  intro x hq hr
  have hp : p.eval x = 0 := by
    simpa [eval_mod_of_eval_eq_zero p hq] using hr
  exact h x hp hq

/-- Signed Euclidean remainders, including the final nonzero constant when appropriate. -/
def signedRemChain (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  if q = 0 then [p] else p :: signedRemChain q (-(p % q))
termination_by q.degree

decreasing_by
  simpa only [degree_neg] using degree_mod_lt p (by assumption)

@[simp] theorem signedRemChain_zero (p : Polynomial ℝ) : signedRemChain p 0 = [p] := by
  rw [signedRemChain]
  simp

theorem signedRemChain_of_ne_zero (p : Polynomial ℝ) {q : Polynomial ℝ} (hq : q ≠ 0) :
    signedRemChain p q = p :: signedRemChain q (-(p % q)) := by
  rw [signedRemChain, if_neg hq]

@[simp] theorem signedRemChain_head (p q : Polynomial ℝ) :
    (signedRemChain p q).head? = some p := by
  rw [signedRemChain]
  split_ifs <;> simp

@[simp] theorem signedRemChain_get_zero (p q : Polynomial ℝ) :
    (signedRemChain p q)[0]? = some p := by
  rw [signedRemChain]
  split_ifs <;> simp

@[simp] theorem signedRemChain_nonempty (p q : Polynomial ℝ) : signedRemChain p q ≠ [] := by
  intro h
  have hh := signedRemChain_head p q
  simp [h] at hh

/-- A nonzero second polynomial is literally the second entry of the constructed chain. -/
theorem signedRemChain_pair (p : Polynomial ℝ) {q : Polynomial ℝ} (hq : q ≠ 0) :
    ∃ tail, signedRemChain p q = p :: q :: tail := by
  rw [signedRemChain_of_ne_zero p hq]
  by_cases hr : -(p % q) = 0
  · exact ⟨[], by simp [hr]⟩
  · exact ⟨signedRemChain (-(p % q)) (-(q % (-(p % q)))),
      by rw [signedRemChain_of_ne_zero q hr]⟩

/-- Every entry is nonzero provided the first is nonzero. -/
theorem signedRemChain_nonzero {p q : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ r ∈ signedRemChain p q, r ≠ 0 := by
  induction p, q using signedRemChain.induct with
  | case1 p =>
      simpa using hp
  | case2 p q hq ih =>
      rw [signedRemChain_of_ne_zero p hq]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp
      · exact ih hq r hr

/-- The final chain member has no real root when the initial pair has none in common. -/
theorem signedRemChain_last {p q : Polynomial ℝ} (hp : p ≠ 0) (h : NoCommonRealRoot p q) :
    ∀ r, (signedRemChain p q).getLast? = some r → ∀ x, r.eval x ≠ 0 := by
  induction p, q using signedRemChain.induct with
  | case1 p =>
      intro r hr x hx
      have hpr : p = r := by simpa using hr
      exact h x (hpr ▸ hx) (by simp)
  | case2 p q hq ih =>
      intro r hr
      apply ih hq h.remainder r
      rw [signedRemChain_of_ne_zero p hq] at hr
      have hne := signedRemChain_nonempty q (-(p % q))
      cases hs : signedRemChain q (-(p % q)) with
      | nil => exact (hne hs).elim
      | cons u us => simpa [hs] using hr

/-- Zeros of an interior remainder are flanked by nonzero opposite-sign values. -/
theorem signedRemChain_interior {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p q) :
    ∀ (i : ℕ) (x : ℝ) (a b c : Polynomial ℝ),
      (signedRemChain p q)[i]? = some a →
      (signedRemChain p q)[i + 1]? = some b →
      (signedRemChain p q)[i + 2]? = some c → b.eval x = 0 →
      a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0 := by
  induction p, q using signedRemChain.induct with
  | case1 p =>
      intro i x a b c h0 h1 h2 hb
      cases i <;> simp_all
  | case2 p q hq ih =>
      intro i x a b c h0 h1 h2 hb
      rw [signedRemChain_of_ne_zero p hq] at h0 h1 h2
      cases i with
      | zero =>
          have hpa : p = a := by simpa using h0
          have hqb : q = b := by
            simpa only [Nat.zero_add, List.getElem?_cons_succ,
              signedRemChain_get_zero, Option.some.injEq] using h1
          subst a
          subst b
          by_cases hr : -(p % q) = 0
          · simp [hr] at h2
          have hrc : -(p % q) = c := by
            simpa only [Nat.zero_add, List.getElem?_cons_succ,
              signedRemChain_of_ne_zero q hr, signedRemChain_get_zero, Option.some.injEq] using h2
          subst c
          have hpx : p.eval x ≠ 0 := fun hp0 => h x hp0 hb
          have heq : (-(p % q)).eval x = -p.eval x := by
            simp [eval_mod_of_eval_eq_zero p hb]
          refine ⟨hpx, ?_, ?_⟩
          · simpa [heq] using hpx
          · rw [heq]
            nlinarith [sq_pos_of_ne_zero hpx]
      | succ i =>
          apply ih hq h.remainder i x a b c
          · simpa using h0
          · simpa [Nat.add_assoc] using h1
          · simpa [Nat.add_assoc] using h2
          · exact hb

end QuantumBehaviors.Projection
