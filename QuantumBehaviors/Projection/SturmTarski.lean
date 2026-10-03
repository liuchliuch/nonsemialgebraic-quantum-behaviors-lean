import QuantumBehaviors.Projection.WeightedSturm
import QuantumBehaviors.Projection.FiniteJumps

/-!
# Weighted variation and Sturm–Tarski queries

The finite signed-jump argument counts the orientations of the first pair of an explicit
Euclidean chain. In the coprime separable case this computes the Tarski query exactly.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Polynomial Sturm Set
open scoped Topology

/-- The signed variation formula between generic endpoints. -/
theorem signedRemChain_weighted_Ioo {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p q) (hderiv : NoCommonRealRoot p p.derivative)
    {a b : ℝ} (hab : a ≤ b)
    (ha : a ∉ chainZeros (signedRemChain p q))
    (hb : b ∉ chainZeros (signedRemChain p q)) :
    (sturmVar (signedRemChain p q) a : ℤ) - sturmVar (signedRemChain p q) b =
      ∑ r ∈ (chainZeros (signedRemChain p q)).filter (fun r => a < r ∧ r < b),
        if p.eval r = 0 then (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0 := by
  have hreg := signedRemChain_regular hp h
  apply finite_jump_sum _ _ _ ?_ ?_ hab ha hb
  · intro u v huv hclear
    have heq : sturmVar (signedRemChain p q) u = sturmVar (signedRemChain p q) v := by
      apply sturmVar_const_of_no_zero u v huv
      intro s hs x hx hzero
      exact hclear x hx ((mem_chainZeros hreg.nonzero_mem).mpr ⟨s, hs, hzero⟩)
    exact congrArg (fun n : ℕ => (n : ℤ)) heq
  · intro r hr u v hur hrv hclear
    have hz : ∀ s ∈ signedRemChain p q, ∀ x ∈ Icc u v, x ≠ r → s.eval x ≠ 0 := by
      intro s hs x hx hxr hzero
      exact hclear x hx hxr ((mem_chainZeros hreg.nonzero_mem).mpr ⟨s, hs, hzero⟩)
    by_cases hpr : p.eval r = 0
    · have hqr := h r hpr
      have hqn : q ≠ 0 := fun hq0 => hqr (by simp [hq0])
      obtain ⟨tail, hshape⟩ := signedRemChain_pair p hqn
      rw [hshape] at hreg hz ⊢
      simpa only [if_pos hpr] using regularChain_root_cross hreg r hpr
        (hderiv r hpr) hqr u v hur hrv hz
    · have hv := regularChain_interior_cross hreg r hpr u v hur hrv hz
      simp only [if_neg hpr]
      rw [hv.1.trans hv.2]
      exact sub_self _

/-- Whole-line weighted variation, with every real root counted once. -/
theorem signedRemChain_weighted {p q : Polynomial ℝ} (hp : p ≠ 0)
    (h : NoCommonRealRoot p q) (hderiv : NoCommonRealRoot p p.derivative) :
    (sturmVarNegInf (signedRemChain p q) : ℤ) - sturmVarPosInf (signedRemChain p q) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  classical
  let chain := signedRemChain p q
  let S := chainZeros chain
  have hreg : RegularChain p chain := signedRemChain_regular hp h
  have hSne : (insert (0 : ℝ) (S.image abs)).Nonempty := ⟨0, by simp⟩
  let M := (insert (0 : ℝ) (S.image abs)).max' hSne + 1
  have hMpos : 0 < M := by
    have := Finset.le_max' (insert (0 : ℝ) (S.image abs)) 0 (by simp)
    dsimp [M]
    linarith
  have hbound : ∀ r ∈ S, |r| < M := by
    intro r hr
    have hle := Finset.le_max' (insert (0 : ℝ) (S.image abs)) |r|
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
    dsimp [M]
    linarith
  have ha : -M ∉ S := by
    intro hm
    have := hbound (-M) hm
    rw [abs_neg, abs_of_pos hMpos] at this
    exact lt_irrefl _ this
  have hb : M ∉ S := by
    intro hm
    have := hbound M hm
    rw [abs_of_pos hMpos] at this
    exact lt_irrefl _ this
  have hall : S.filter (fun r => -M < r ∧ r < M) = S := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    exact abs_lt.mp (hbound r hr)
  have hV := signedRemChain_weighted_Ioo hp h hderiv (a := -M) (b := M)
    (by linarith) ha hb
  change (sturmVar chain (-M) : ℤ) - sturmVar chain M =
    ∑ r ∈ S.filter (fun r => -M < r ∧ r < M), _ at hV
  rw [hall] at hV
  have hpos : sturmVar chain M = sturmVarPosInf chain := by
    apply signVariations_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro s hs
    apply eval_sign_pos_inf (hreg.nonzero_mem s hs)
    intro r hr
    exact (abs_lt.mp (hbound r ((mem_chainZeros hreg.nonzero_mem).mpr ⟨s, hs, hr⟩))).2
  have hneg : sturmVar chain (-M) = sturmVarNegInf chain := by
    apply signVariations_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro s hs
    apply eval_sign_neg_inf (hreg.nonzero_mem s hs)
    intro r hr
    exact (abs_lt.mp (hbound r ((mem_chainZeros hreg.nonzero_mem).mpr ⟨s, hs, hr⟩))).1
  rw [hpos, hneg] at hV
  have hsubset : p.roots.toFinset ⊆ S := by
    intro r hr
    exact (mem_chainZeros hreg.nonzero_mem).mpr ⟨p, hreg.head_mem,
      (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hr)⟩
  refine hV.trans ?_
  calc
    (∑ r ∈ S, if p.eval r = 0 then (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0) =
        ∑ r ∈ p.roots.toFinset,
          if p.eval r = 0 then (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro r hr hnr
      apply if_neg
      intro hzero
      exact hnr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hzero))
    _ = ∑ r ∈ p.roots.toFinset, (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hz : p.eval r = 0 := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
      rw [if_pos hz]

/-- Sturm–Tarski with simple real roots and a weight nonzero at those roots. -/
theorem sturmTarski_simple {p q : Polynomial ℝ} (hp : p ≠ 0)
    (hd : NoCommonRealRoot p p.derivative)
    (h : NoCommonRealRoot p q) :
    tarskiQuery p.roots.toFinset q =
      (sturmVarNegInf (signedRemChain p (p.derivative * q)) : ℤ) -
        sturmVarPosInf (signedRemChain p (p.derivative * q)) := by
  have hpair : NoCommonRealRoot p (p.derivative * q) := by
    intro r hr
    simpa only [eval_mul] using mul_ne_zero (hd r hr) (h r hr)
  rw [signedRemChain_weighted hp hpair hd]
  unfold tarskiQuery
  apply Finset.sum_congr rfl
  intro r hr
  have hpr := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
  have heq : p.derivative.eval r * (p.derivative * q).eval r =
      p.derivative.eval r ^ 2 * q.eval r := by rw [eval_mul]; ring
  rw [heq, sign_mul, sign_pos (sq_pos_of_ne_zero (hd r hpr)), one_mul]

/-- Sturm–Tarski for a separable denominator and a weight nonzero at every real root. -/
theorem sturmTarski_coprime {p q : Polynomial ℝ} (hp : p ≠ 0) (hsep : p.Separable)
    (h : NoCommonRealRoot p q) :
    tarskiQuery p.roots.toFinset q =
      (sturmVarNegInf (signedRemChain p (p.derivative * q)) : ℤ) -
        sturmVarPosInf (signedRemChain p (p.derivative * q)) := by
  have hd := noCommonRealRoot_derivative hsep
  have hpair : NoCommonRealRoot p (p.derivative * q) := by
    intro r hr
    simpa only [eval_mul] using mul_ne_zero (hd r hr) (h r hr)
  rw [signedRemChain_weighted hp hpair hd]
  unfold tarskiQuery
  apply Finset.sum_congr rfl
  intro r hr
  have hpr := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
  have heq : p.derivative.eval r * (p.derivative * q).eval r =
      p.derivative.eval r ^ 2 * q.eval r := by rw [eval_mul]; ring
  rw [heq, sign_mul, sign_pos (sq_pos_of_ne_zero (hd r hpr)), one_mul]

end QuantumBehaviors.Projection
