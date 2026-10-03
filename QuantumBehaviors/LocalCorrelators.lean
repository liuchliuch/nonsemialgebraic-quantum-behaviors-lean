import QuantumBehaviors.Nonlocality

/-! The explicit local model for every correlator matrix along the nonlocal curve. -/
namespace QuantumBehaviors

open scoped BigOperators

/-- A finite hidden-variable type can be reindexed to the finite-locality definition. -/
theorem bellLocal_of_fintype {ι : Type*} [Fintype ι] (p : Behavior) (w : ι → ℝ)
    (A B : ι → Response) (hw : ∀ k, 0 ≤ w k) (hsum : (∑ k, w k) = 1)
    (hreal : ∀ x, p x = ∑ k, w k * deterministic (A k) (B k) x) : BellLocal p := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun k => w (e k), fun k => A (e k), fun k => B (e k),
    fun k => hw (e k), ?_, ?_⟩
  · exact (Equiv.sum_comp e w).trans hsum
  · intro x
    exact (hreal x).trans (Equiv.sum_comp e (fun k => w k * deterministic (A k) (B k) x)).symm

theorem BellLocal.convex_combination {p q : Behavior} (hp : BellLocal p) (hq : BellLocal q)
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) : BellLocal (t • p + u • q) := by
  obtain ⟨n, w, A, B, hw, hsumw, hrealw⟩ := hp
  obtain ⟨m, v, C, D, hv, hsumv, hrealv⟩ := hq
  apply bellLocal_of_fintype (t • p + u • q)
    (Sum.elim (fun k => t * w k) (fun k => u * v k)) (Sum.elim A C) (Sum.elim B D)
  · intro k
    cases k with
    | inl k => exact mul_nonneg ht (hw k)
    | inr k => exact mul_nonneg hu (hv k)
  · simp [Fintype.sum_sum_type, ← Finset.mul_sum, hsumw, hsumv, htu]
  · intro x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, hrealw, hrealv, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring

/-- All sixteen four-bit strings. -/
def unrestrictedResponses : Fin 16 → Response :=
  ![![false,false,false,false], ![false,false,false,true],
    ![false,false,true,false], ![false,false,true,true],
    ![false,true,false,false], ![false,true,false,true],
    ![false,true,true,false], ![false,true,true,true],
    ![true,false,false,false], ![true,false,false,true],
    ![true,false,true,false], ![true,false,true,true],
    ![true,true,false,false], ![true,true,false,true],
    ![true,true,true,false], ![true,true,true,true]]

noncomputable def independentBehavior : Behavior := fun x =>
  ∑ k : Fin 16, (1 / 16 : ℝ) * deterministic (unrestrictedResponses k) (unrestrictedResponses k) x

theorem independentBehavior_local : BellLocal independentBehavior := by
  refine ⟨16, fun _ => 1 / 16, unrestrictedResponses, unrestrictedResponses, ?_, ?_, ?_⟩
  · intro k
    norm_num
  · norm_num
  · intro x
    rfl

theorem independentBehavior_correlator (i j : Input) :
    correlator independentBehavior i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [correlator, independentBehavior, unrestrictedResponses, deterministic, Fin.sum_univ_succ]

theorem correlator_linear (p q : Behavior) (t u : ℝ) (i j : Input) :
    correlator (t • p + u • q) i j = t * correlator p i j + u * correlator q i j := by
  simp only [correlator, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def curveCorrelator (α : ℝ) : ℝ := ((α - 2) ^ 2 - 1) / 3

noncomputable def localCorrelatorModel (α : ℝ) : Behavior :=
  (-3 * curveCorrelator α) • balancedBehavior + (1 + 3 * curveCorrelator α) • independentBehavior

theorem localCorrelatorModel_local {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    BellLocal (localCorrelatorModel α) := by
  apply balancedBehavior_local.convex_combination independentBehavior_local
  · unfold curveCorrelator
    have h := mul_nonneg (show 0 ≤ α - 1 by linarith) (show 0 ≤ 3 - α by linarith)
    nlinarith
  · unfold curveCorrelator
    nlinarith [sq_nonneg (α - 2)]
  · ring

theorem localCorrelatorModel_exact (α : ℝ) (i j : Input) :
    correlator (localCorrelatorModel α) i j = correlator (curve α) i j := by
  rw [localCorrelatorModel, correlator_linear, ← curve_two_eq_balanced,
    independentBehavior_correlator]
  by_cases hij : i = j
  · subst j
    simp only [curve_correlator_diagonal, ↓reduceIte]
    ring
  · rw [curve_correlator_offdiagonal 2 hij, curve_correlator_offdiagonal α hij, if_neg hij]
    unfold curveCorrelator
    ring

/-- Proposition S13, including the distinction between the full behavior and its correlators. -/
theorem proposition_S13 {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    ¬ BellLocal (curve α) ∧ ∃ q : Behavior, BellLocal q ∧
      ∀ i j, correlator q i j = correlator (curve α) i j := by
  exact ⟨curve_not_bellLocal hα₁ hα₂, localCorrelatorModel α,
    localCorrelatorModel_local hα₁ hα₂, localCorrelatorModel_exact α⟩

end QuantumBehaviors
