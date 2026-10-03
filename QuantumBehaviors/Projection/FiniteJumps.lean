import QuantumBehaviors.Projection.Vendored.SturmTheorem

/-!
# Telescoping finitely many signed jumps

The endpoint values are taken away from the finite break set, so negative and positive
jumps are treated symmetrically without an endpoint-registration convention.
-/

noncomputable section

namespace QuantumBehaviors.Projection

open Set

/-- A function constant between finitely many breaks telescopes the signed local jumps. -/
theorem finite_jump_sum (S : Finset ℝ) (V w : ℝ → ℤ)
    (hconst : ∀ a b : ℝ, a ≤ b → (∀ x ∈ Icc a b, x ∉ S) → V a = V b)
    (hcross : ∀ r ∈ S, ∀ a b : ℝ, a < r → r < b →
      (∀ x ∈ Icc a b, x ≠ r → x ∉ S) → V a - V b = w r)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∉ S) (hb : b ∉ S) :
    V a - V b = ∑ r ∈ S.filter (fun r => a < r ∧ r < b), w r := by
  classical
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b → a ∉ S → b ∉ S →
      (S.filter (fun r => a < r ∧ r < b)).card = n →
      V a - V b = ∑ r ∈ S.filter (fun r => a < r ∧ r < b), w r by
    exact H _ a b hab ha hb rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a b hab ha hb hcard
      let F := S.filter (fun r => a < r ∧ r < b)
      by_cases hF : F.Nonempty
      · let z := F.max' hF
        have hzF : z ∈ F := F.max'_mem hF
        have hz : z ∈ S ∧ a < z ∧ z < b := Finset.mem_filter.mp hzF
        obtain ⟨a', haa', ha'z, hgap⟩ := Sturm.exists_left_gap S z a hz.2.1
        have ha'S : a' ∉ S := by
          intro h
          exact lt_irrefl a' (hgap a' h ha'z)
        let F' := S.filter (fun r => a < r ∧ r < a')
        have hznot : z ∉ F' := by
          intro h
          exact (not_lt_of_ge ha'z.le) (Finset.mem_filter.mp h).2.2
        have hsplit : F = insert z F' := by
          ext x
          constructor
          · intro hx
            by_cases hxz : x = z
            · simp [hxz]
            · have hxl : x < z := lt_of_le_of_ne (F.le_max' x hx) hxz
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
                ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1,
                  hgap x (Finset.mem_filter.mp hx).1 hxl⟩))
          · intro hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hzF
            · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
                (Finset.mem_filter.mp hx).2.1,
                lt_trans (Finset.mem_filter.mp hx).2.2 (lt_trans ha'z hz.2.2)⟩
        have hsmaller : F'.card < n := by
          change F.card = n at hcard
          rw [hsplit, Finset.card_insert_of_notMem hznot] at hcard
          omega
        have hIH := ih _ hsmaller a a' haa'.le ha ha'S rfl
        have hcross' : V a' - V b = w z := by
          apply hcross z hz.1 a' b ha'z hz.2.2
          intro x hx hxz hxS
          rcases lt_trichotomy x z with hlt | heq | hgt
          · exact not_lt_of_ge hx.1 (hgap x hxS hlt)
          · exact hxz heq
          · have hxb : x < b := lt_of_le_of_ne hx.2 (fun h => hb (h ▸ hxS))
            have hxF : x ∈ F := Finset.mem_filter.mpr
              ⟨hxS, lt_of_lt_of_le haa' hx.1, hxb⟩
            exact not_le_of_gt hgt (F.le_max' x hxF)
        change V a - V b = ∑ r ∈ F, w r
        rw [hsplit, Finset.sum_insert hznot]
        change V a - V a' = ∑ r ∈ F', w r at hIH
        omega
      · have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
        have hclear : ∀ x ∈ Icc a b, x ∉ S := by
          intro x hx hxS
          have hax : a < x := lt_of_le_of_ne hx.1 (fun h => ha (h.symm ▸ hxS))
          have hxb : x < b := lt_of_le_of_ne hx.2 (fun h => hb (h ▸ hxS))
          exact hF ⟨x, Finset.mem_filter.mpr ⟨hxS, hax, hxb⟩⟩
        change V a - V b = ∑ r ∈ F, w r
        rw [hconst a b hab hclear, hempty]
        simp

end QuantumBehaviors.Projection
