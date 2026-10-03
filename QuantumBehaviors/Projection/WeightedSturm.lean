import QuantumBehaviors.Projection.SturmCount
import QuantumBehaviors.Projection.SignDetermination

/-!
# Weighted Sturm chain infrastructure

The interior sign conditions are independent of the orientation of the first pair.
This file separates those conditions, proves variation-neutral interior crossings, and
proves the signed local contribution of root crossings in either orientation.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Filter Polynomial Sturm
open scoped Topology

/-- The Sturm conditions that do not impose an orientation at roots of the first entry. -/
structure RegularChain (p : Polynomial ℝ) (chain : List (Polynomial ℝ)) : Prop where
  head : chain.head? = some p
  nonzero_mem : ∀ q ∈ chain, q ≠ 0
  interior_alternates : ∀ (i : ℕ) (x : ℝ) (a b c : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → chain[i + 2]? = some c →
    b.eval x = 0 → a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  last_no_root : ∀ q : Polynomial ℝ, chain.getLast? = some q → ∀ x : ℝ, q.eval x ≠ 0

lemma RegularChain.head_mem {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}
    (h : RegularChain p chain) : p ∈ chain := List.mem_of_head? h.head

lemma signedRemChain_regular {p q : Polynomial ℝ} (hp : p ≠ 0) (h : NoCommonRealRoot p q) :
    RegularChain p (signedRemChain p q) where
  head := signedRemChain_head _ _
  nonzero_mem := signedRemChain_nonzero hp
  interior_alternates := signedRemChain_interior hp h
  last_no_root := signedRemChain_last hp h

/-- Neutral crossing for a regular chain whose first entry does not vanish. -/
theorem regularChain_interior_cross {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}
    (hchain : RegularChain p chain) (r : ℝ) (hpr : p.eval r ≠ 0)
    (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain r ∧ sturmVar chain r = sturmVar chain b := by
  have hab : a ≤ b := (har.trans hrb).le
  have hfront : ∀ q, chain.head? = some q → q.eval r ≠ 0 := by
    intro q hq
    rw [hchain.head] at hq
    cases hq
    exact hpr
  have hlast : ∀ q, chain.getLast? = some q → q.eval r ≠ 0 :=
    fun q hq => hchain.last_no_root q hq r
  have halt : ∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), chain[i]? = some q0 →
      chain[i + 1]? = some q1 → chain[i + 2]? = some q2 → q1.eval r = 0 →
      q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0 :=
    fun i q0 q1 q2 => hchain.interior_alternates i r q0 q1 q2
  have ha := signRelation_eval a r chain
    (fun q hq => hz q hq a ⟨le_rfl, hab⟩ (ne_of_lt har)) hfront hlast halt
    (fun q hq hqr => eval_sign_eq_of_no_zero har.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr))
  have hb := signRelation_eval b r chain
    (fun q hq => hz q hq b ⟨hab, le_rfl⟩ (ne_of_lt hrb).symm) hfront hlast halt
    (fun q hq hqr => (eval_sign_eq_of_no_zero hrb.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm)
  exact ⟨ha.signVariations_eq.1, hb.signVariations_eq.1.symm⟩

/-- Removing the first member preserves the regular-chain conditions. -/
lemma RegularChain.tail {p q : Polynomial ℝ} {tail : List (Polynomial ℝ)}
    (h : RegularChain p (p :: q :: tail)) : RegularChain q (q :: tail) where
  head := rfl
  nonzero_mem := fun r hr => h.nonzero_mem r (List.mem_cons_of_mem _ hr)
  interior_alternates := by
    intro i x a b c h0 h1 h2 hb
    apply h.interior_alternates (i + 1) x a b c
    · simpa using h0
    · simpa [Nat.add_assoc] using h1
    · simpa [Nat.add_assoc] using h2
    · exact hb
  last_no_root := by
    intro r hr x
    apply h.last_no_root r ?_ x
    simpa using hr

/-- The entire change is the change in the head pair when the tail's variations agree. -/
lemma head_pair_variation_difference (p q : Polynomial ℝ) (tail : List (Polynomial ℝ))
    (a b : ℝ) (hpa : p.eval a ≠ 0) (hpb : p.eval b ≠ 0)
    (hqa : q.eval a ≠ 0) (hqb : q.eval b ≠ 0)
    (htail : sturmVar (q :: tail) a = sturmVar (q :: tail) b) :
    (sturmVar (p :: q :: tail) a : ℤ) - sturmVar (p :: q :: tail) b =
      (if p.eval a * q.eval a < 0 then (1 : ℤ) else 0) -
      (if p.eval b * q.eval b < 0 then (1 : ℤ) else 0) := by
  have ha : sturmVar (p :: q :: tail) a =
      (if p.eval a * q.eval a < 0 then 1 else 0) + sturmVar (q :: tail) a := by
    simp only [sturmVar, List.map_cons, signVariations_cons _ hpa,
      firstSign_cons_ne _ hqa, ← sign_mul, sign_eq_neg_one_iff]
  have hb : sturmVar (p :: q :: tail) b =
      (if p.eval b * q.eval b < 0 then 1 else 0) + sturmVar (q :: tail) b := by
    simp only [sturmVar, List.map_cons, signVariations_cons _ hpb,
      firstSign_cons_ne _ hqb, ← sign_mul, sign_eq_neg_one_iff]
  rw [ha, hb, htail]
  split_ifs <;> simp

/-- At a simple root, the first-pair crossing has the sign of `p'(r) q(r)`. -/
lemma simple_root_pair_sign {p q : Polynomial ℝ} {r : ℝ} (hr : p.eval r = 0)
    (hd : p.derivative.eval r ≠ 0) (hq : q.eval r ≠ 0) :
    (∀ᶠ x in 𝓝[<] r, SignType.sign ((p * q).eval x) =
      -SignType.sign (p.derivative.eval r * q.eval r)) ∧
    (∀ᶠ x in 𝓝[>] r, SignType.sign ((p * q).eval x) =
      SignType.sign (p.derivative.eval r * q.eval r)) := by
  obtain ⟨s, hs⟩ := (Polynomial.dvd_iff_isRoot.mpr hr : X - C r ∣ p)
  have hsderiv : p.derivative.eval r = s.eval r := by
    rw [hs]
    simp [derivative_mul]
  have hn : s.eval r * q.eval r ≠ 0 := by rw [← hsderiv]; exact mul_ne_zero hd hq
  have hc : ContinuousAt (fun x : ℝ => s.eval x * q.eval x) r := by fun_prop
  have hevent : ∀ᶠ x in 𝓝 r, SignType.sign (s.eval x * q.eval x) =
      SignType.sign (p.derivative.eval r * q.eval r) := by
    rw [hsderiv]
    exact ((continuousAt_sign_of_ne_zero hn).comp
      (f := fun x : ℝ => s.eval x * q.eval x) hc).tendsto.eventually
      (isOpen_discrete _ |>.mem_nhds (by simp : SignType.sign (s.eval r * q.eval r) ∈
        {SignType.sign (s.eval r * q.eval r)}))
  have heq (x : ℝ) : (p * q).eval x = (x - r) * (s.eval x * q.eval x) := by
    rw [eval_mul, hs, eval_mul]
    simp only [eval_sub, eval_X, eval_C]
    ring
  constructor
  · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxr
    rw [heq, sign_mul, sign_neg (sub_neg.mpr hxr), hx]
    simp
  · filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxr
    rw [heq, sign_mul, sign_pos (sub_pos.mpr hxr), hx, one_mul]

/-- The local signed drop in variations, allowing either orientation at the root. -/
theorem regularChain_root_cross {p q : Polynomial ℝ} {tail : List (Polynomial ℝ)}
    (hchain : RegularChain p (p :: q :: tail)) (r : ℝ) (hr : p.eval r = 0)
    (hd : p.derivative.eval r ≠ 0) (hq : q.eval r ≠ 0)
    (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ s ∈ p :: q :: tail, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0) :
    (sturmVar (p :: q :: tail) a : ℤ) - sturmVar (p :: q :: tail) b =
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  have hab : a ≤ b := (har.trans hrb).le
  obtain ⟨hflL, hflR⟩ := simple_root_pair_sign hr hd hq
  have htail := regularChain_interior_cross hchain.tail r hq a b har hrb
    (fun s hs => hz s (List.mem_cons_of_mem _ hs))
  have hpa := hz p (by simp) a ⟨le_rfl, hab⟩ (ne_of_lt har)
  have hpb := hz p (by simp) b ⟨hab, le_rfl⟩ (ne_of_lt hrb).symm
  have hqa := hz q (by simp) a ⟨le_rfl, hab⟩ (ne_of_lt har)
  have hqb := hz q (by simp) b ⟨hab, le_rfl⟩ (ne_of_lt hrb).symm
  have hsignA : SignType.sign (p.eval a * q.eval a) =
      -SignType.sign (p.derivative.eval r * q.eval r) := by
    obtain ⟨c, hc, hcmem⟩ := (hflL.and (Ioo_mem_nhdsLT har)).exists
    have heq := eval_sign_eq_of_no_zero hcmem.1.le (q := p * q) (fun x hx => by
      rw [eval_mul]
      have hxr : x ≠ r := ne_of_lt (lt_of_le_of_lt hx.2 hcmem.2)
      have hxab : x ∈ Set.Icc a b := ⟨hx.1, hx.2.trans (hcmem.2.le.trans hrb.le)⟩
      exact mul_ne_zero (hz p (by simp) x hxab hxr) (hz q (by simp) x hxab hxr))
    exact (by simpa only [eval_mul] using heq.trans hc)
  have hsignB : SignType.sign (p.eval b * q.eval b) =
      SignType.sign (p.derivative.eval r * q.eval r) := by
    obtain ⟨c, hc, hcmem⟩ := (hflR.and (Ioo_mem_nhdsGT hrb)).exists
    have heq := eval_sign_eq_of_no_zero hcmem.2.le (q := p * q) (fun x hx => by
      rw [eval_mul]
      have hxr : x ≠ r := (ne_of_lt (lt_of_lt_of_le hcmem.1 hx.1)).symm
      have hxab : x ∈ Set.Icc a b := ⟨har.le.trans (hcmem.1.le.trans hx.1), hx.2⟩
      exact mul_ne_zero (hz p (by simp) x hxab hxr) (hz q (by simp) x hxab hxr))
    exact (by simpa only [eval_mul] using heq.symm.trans hc)
  rw [head_pair_variation_difference p q tail a b hpa hpb hqa hqb (htail.1.trans htail.2)]
  have hn : SignType.sign (p.derivative.eval r * q.eval r) ≠ 0 := by
    simpa only [ne_eq, sign_eq_zero_iff] using mul_ne_zero hd hq
  simp only [← sign_eq_neg_one_iff, hsignA, hsignB]
  generalize SignType.sign (p.derivative.eval r * q.eval r) = w at hn ⊢
  cases w <;> simp_all

end QuantumBehaviors.Projection
