import QuantumBehaviors.Projection.UniformTarski

/-! # Uniform finite quantifier-free descriptions of root-sign conditions -/

noncomputable section

namespace QuantumBehaviors

namespace SignFormula

def bindSigns {ι κ : Type*} (f : ι → SignType → SignFormula κ) : SignFormula ι → SignFormula κ
  | .truth b => .truth b
  | .atom i s => f i s
  | .conj p q => .conj (bindSigns f p) (bindSigns f q)
  | .disj p q => .disj (bindSigns f p) (bindSigns f q)
  | .neg p => .neg (bindSigns f p)

lemma eval_bindSigns {ι κ : Type*} (f : ι → SignType → SignFormula κ)
    (v : κ → SignType) (w : ι → SignType)
    (h : ∀ i s, (f i s).eval v = decide (w i = s)) (φ : SignFormula ι) :
    (φ.bindSigns f).eval v = φ.eval w := by
  induction φ <;> simp_all [bindSigns, eval]

end SignFormula

namespace Projection

open Polynomial
attribute [local instance] Classical.propDecidable

variable {ι α : Type*}

theorem isSemialgebraic_finite_exists [Fintype α] (C : α → Set (ι → ℝ))
    (hC : ∀ a, IsSemialgebraic (C a)) : IsSemialgebraic {x : ι → ℝ | ∃ a, x ∈ C a} := by
  classical
  choose φ hφ using fun a => isSemialgebraic_iff_formula.mp (hC a)
  refine isSemialgebraic_iff_formula.mpr ⟨SignFormula.any (Finset.univ.toList.map φ), ?_⟩
  intro x
  simp only [PolynomialSignFormula.realize, SignFormula.eval_any]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨φ a, List.mem_map.mpr ⟨a, by simp, rfl⟩, (hφ a x).mp ha⟩
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨a, (hφ a x).mpr hpx⟩

/-- Substitution of rational-tree sign tests into arbitrary finite Boolean syntax. -/
theorem isSemialgebraic_rational_formula (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ i, RationallyRepresentable (f i)) (φ : SignFormula α) :
    IsSemialgebraic {x : ι → ℝ | φ.eval (fun i => SignType.sign (f i x)) = true} := by
  classical
  choose t ht using hf
  refine isSemialgebraic_iff_formula.mpr
    ⟨φ.bindSigns (fun i s => (t i).signFormula s), ?_⟩
  intro x
  change φ.eval (fun i => SignType.sign (f i x)) = true ↔ _
  have heq := SignFormula.eval_bindSigns (fun i s => (t i).signFormula s)
    (fun p => SignType.sign (MvPolynomial.eval x p)) (fun i => SignType.sign (f i x))
    (fun i s => by
      have h := (t i).signFormula_correct s x
      rw [ht] at h
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using h)) φ
  exact (iff_of_eq (congrArg (· = true) heq)).symm

namespace RationalPolynomialMap

variable {F : (ι → ℝ) → Polynomial ℝ}

theorem pow (hF : RationalPolynomialMap F) (n : ℕ) :
    RationalPolynomialMap (fun x => F x ^ n) := by
  induction n with
  | zero => simpa using RationalPolynomialMap.const (ι := ι) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem finset_prod (s : Finset α) (F : α → (ι → ℝ) → Polynomial ℝ)
    (hF : ∀ i ∈ s, RationalPolynomialMap (F i)) :
    RationalPolynomialMap (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RationalPolynomialMap.const (ι := ι) 1
  | @insert a s has ih =>
      simpa only [Finset.prod_insert has] using (hF a (by simp)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end RationalPolynomialMap

/-- Every specified sign pattern at a real root has a genuine finite sign description. -/
theorem isSemialgebraic_root_signs [Fintype α] [DecidableEq α]
    (P : (ι → ℝ) → Polynomial ℝ) (Q : α → (ι → ℝ) → Polynomial ℝ)
    (hP : RationalPolynomialMap P) (hQ : ∀ i, RationalPolynomialMap (Q i))
    (target : α → SignType) :
    IsSemialgebraic {x : ι → ℝ | ∃ t ∈ (P x).roots.toFinset,
      ∀ i, SignType.sign ((Q i x).eval t) = target i} := by
  classical
  let g := fun x => ∑ e : α → Fin 3, (∏ i, signWeight (target i) (e i)) *
    tarskiAlgorithm (P x) (queryPolynomial (fun i => Q i x) e)
  have hrep : RationallyRepresentable (fun x => (g x : ℝ)) := by
    unfold g
    simp only [Int.cast_sum, Int.cast_mul]
    apply RationallyRepresentable.finset_sum
    intro e he
    apply (RationallyRepresentable.const _).mul
    apply hP.tarskiAlgorithm
    exact RationalPolynomialMap.finset_prod Finset.univ
      (fun i x => Q i x ^ (e i : ℕ)) (fun i _ => (hQ i).pow _)
  convert hrep.isSemialgebraic_sign 1 using 1
  ext x
  simp only [Set.mem_setOf_eq, sign_eq_one_iff, Int.cast_pos]
  exact (signDetermination_algorithm (P x) (fun i => Q i x) target).symm

/-- Eliminate a real-root sign formula by a finite disjunction over its accepted sign vectors. -/
theorem isSemialgebraic_root_formula [Fintype α] [DecidableEq α]
    (P : (ι → ℝ) → Polynomial ℝ) (Q : α → (ι → ℝ) → Polynomial ℝ)
    (hP : RationalPolynomialMap P) (hQ : ∀ i, RationalPolynomialMap (Q i))
    (φ : SignFormula α) :
    IsSemialgebraic {x : ι → ℝ | ∃ t ∈ (P x).roots.toFinset,
      φ.eval (fun i => SignType.sign ((Q i x).eval t)) = true} := by
  classical
  let C := fun s : α → SignType => {x : ι → ℝ | φ.eval s = true ∧
    ∃ t ∈ (P x).roots.toFinset, ∀ i, SignType.sign ((Q i x).eval t) = s i}
  have hC : ∀ s, IsSemialgebraic (C s) := by
    intro s
    by_cases hs : φ.eval s = true
    · simpa only [C, hs, true_and] using isSemialgebraic_root_signs P Q hP hQ s
    · simpa [C, hs] using
        (IsSemialgebraic.empty (ι := ι))
  convert isSemialgebraic_finite_exists C hC using 1
  ext x
  constructor
  · rintro ⟨t, ht, hφ⟩
    exact ⟨(fun i => SignType.sign ((Q i x).eval t)), hφ, t, ht, fun _ => rfl⟩
  · rintro ⟨s, hs, t, ht, hsign⟩
    exact ⟨t, ht, by rw [funext hsign]; exact hs⟩

end Projection
end QuantumBehaviors
