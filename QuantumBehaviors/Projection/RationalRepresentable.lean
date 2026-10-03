import QuantumBehaviors.Projection.RationalTree

/-!
# Rationally representable coefficient functions

This is a proved syntax-representation property, not a replacement definition of
semialgebraicity. Every sign test is exported back to `IsSemialgebraic` by the actual
finite rational-tree compiler.
-/

noncomputable section

namespace QuantumBehaviors.Projection

attribute [local instance] Classical.propDecidable

variable {ι α : Type*}

/-- Existence of an actual finite guarded rational expression for a real-valued function. -/
def RationallyRepresentable (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ t : RationalTree ι, ∀ x, t.eval x = f x

namespace RationallyRepresentable

variable {f g : (ι → ℝ) → ℝ}

theorem polynomial (p : MvPolynomial ι ℝ) :
    RationallyRepresentable (fun x => MvPolynomial.eval x p) :=
  ⟨RationalTree.ofPolynomial p, fun x => by simp⟩

theorem const (r : ℝ) : RationallyRepresentable (fun _ : ι → ℝ => r) := by
  simpa using polynomial (MvPolynomial.C r : MvPolynomial ι ℝ)

theorem add (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    RationallyRepresentable (fun x => f x + g x) := by
  obtain ⟨t, ht⟩ := hf
  obtain ⟨u, hu⟩ := hg
  exact ⟨t.add u, fun x => by simp [ht, hu]⟩

theorem mul (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    RationallyRepresentable (fun x => f x * g x) := by
  obtain ⟨t, ht⟩ := hf
  obtain ⟨u, hu⟩ := hg
  exact ⟨t.mul u, fun x => by simp [ht, hu]⟩

theorem inv (hf : RationallyRepresentable f) : RationallyRepresentable (fun x => (f x)⁻¹) := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t.inv, fun x => by simp [ht]⟩

theorem div (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    RationallyRepresentable (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem neg (hf : RationallyRepresentable f) : RationallyRepresentable (fun x => -f x) := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t.neg, fun x => by simp [ht]⟩

theorem sub (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    RationallyRepresentable (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem finset_sum (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ i ∈ s, RationallyRepresentable (f i)) :
    RationallyRepresentable (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) 0
  | @insert a s has ih =>
      simpa only [Finset.sum_insert has] using (hf a (by simp)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ite {C : Set (ι → ℝ)} (hC : IsSemialgebraic C)
    (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    RationallyRepresentable (fun x => if x ∈ C then f x else g x) := by
  classical
  obtain ⟨φ, hφ⟩ := isSemialgebraic_iff_formula.mp hC
  obtain ⟨t, ht⟩ := hf
  obtain ⟨u, hu⟩ := hg
  refine ⟨.branch φ t u, ?_⟩
  intro x
  simp only [RationalTree.eval, ht, hu, ← hφ]

theorem isSemialgebraic_sign (hf : RationallyRepresentable f) (s : SignType) :
    IsSemialgebraic {x : ι → ℝ | SignType.sign (f x) = s} := by
  obtain ⟨t, ht⟩ := hf
  simpa only [ht] using t.isSemialgebraic_sign s

theorem isSemialgebraic_zero (hf : RationallyRepresentable f) :
    IsSemialgebraic {x : ι → ℝ | f x = 0} := by
  simpa only [sign_eq_zero_iff] using hf.isSemialgebraic_sign 0

theorem isSemialgebraic_eq (hf : RationallyRepresentable f) (hg : RationallyRepresentable g) :
    IsSemialgebraic {x : ι → ℝ | f x = g x} := by
  simpa only [sub_eq_zero] using (hf.sub hg).isSemialgebraic_zero

end RationallyRepresentable

/-- Finite conjunction closure with explicit finite output syntax. -/
theorem isSemialgebraic_finite_forall [Fintype α] (C : α → Set (ι → ℝ))
    (hC : ∀ a, IsSemialgebraic (C a)) : IsSemialgebraic {x : ι → ℝ | ∀ a, x ∈ C a} := by
  classical
  choose φ hφ using fun a => isSemialgebraic_iff_formula.mp (hC a)
  refine isSemialgebraic_iff_formula.mpr
    ⟨SignFormula.all (Finset.univ.toList.map φ), ?_⟩
  intro x
  simp only [PolynomialSignFormula.realize, SignFormula.eval_all]
  constructor
  · intro hx p hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact (hφ a x).mp (hx a)
  · intro hx a
    apply (hφ a x).mpr
    exact hx (φ a) (List.mem_map.mpr ⟨a, by simp, rfl⟩)

end QuantumBehaviors.Projection
