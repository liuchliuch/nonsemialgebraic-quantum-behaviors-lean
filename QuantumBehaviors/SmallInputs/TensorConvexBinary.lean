import QuantumBehaviors.Scenarios.Reindex
import QuantumBehaviors.Scenarios.BoundedDimension
import QuantumBehaviors.MatrixEmbedding
import Mathlib.Analysis.Convex.Basic

/-! Genuine convexification by block-local POVMs and an embedded mixed density. -/
namespace QuantumBehaviors.SmallInputs
open Matrix
open scoped BigOperators Kronecker ComplexOrder

lemma block_pair_positive {a b : ℕ} {P : Matrix (Fin a) (Fin a) ℂ} {Q : Matrix (Fin b) (Fin b) ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (Matrix.fromBlocks P 0 0 Q).PosSemidef := by
  obtain ⟨L,hL⟩ := complex_psd_iff_gram P |>.mp hP
  obtain ⟨R,hR⟩ := complex_psd_iff_gram Q |>.mp hQ
  have heq : Matrix.fromBlocks P 0 0 Q = (Matrix.fromBlocks L 0 0 R).conjTranspose*Matrix.fromBlocks L 0 0 R := by
    rw [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
    simp [hL,hR]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma block_pair_sum {J I K : Type*} [Fintype J] [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (P : J → Matrix I I ℂ) (Q : J → Matrix K K ℂ) (hP : ∑ a, P a=1) (hQ : ∑ a, Q a=1) :
    (∑ a, Matrix.fromBlocks (P a) 0 0 (Q a))=1 := by
  have heq : (∑ a, Matrix.fromBlocks (P a) 0 0 (Q a))=Matrix.fromBlocks (∑ a, P a) 0 0 (∑ a, Q a) := by
    ext (i|i) (j|j) <;> simp [Matrix.sum_apply]
  rw [heq,hP,hQ,Matrix.fromBlocks_one]

theorem convex_pair_strategy {nA nB mA mB a₁ b₁ a₂ b₂ : ℕ}
    (s : Scenarios.FiniteStrategy nA nB mA mB a₁ b₁)
    (t : Scenarios.FiniteStrategy nA nB mA mB a₂ b₂)
    {p q : Scenarios.Behavior nA nB mA mB} (hp : s.realizes p) (hq : t.realizes q)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v=1) :
    ∃ r : Scenarios.FiniteStrategy nA nB mA mB (a₁+a₂) (b₁+b₂), r.realizes (u • p+v • q) := by
  let e₁ : Fin a₁ × Fin b₁ → (Fin a₁ ⊕ Fin a₂) × (Fin b₁ ⊕ Fin b₂) := fun x => (Sum.inl x.1,Sum.inl x.2)
  let e₂ : Fin a₂ × Fin b₂ → (Fin a₁ ⊕ Fin a₂) × (Fin b₁ ⊕ Fin b₂) := fun x => (Sum.inr x.1,Sum.inr x.2)
  have he₁ : Function.Injective e₁ := by intro x y h; exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (Sum.inl.inj (congrArg Prod.snd h))
  have he₂ : Function.Injective e₂ := by intro x y h; exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h)) (Sum.inr.inj (congrArg Prod.snd h))
  let ρ := u • embeddedDensity e₁ s.density+v • embeddedDensity e₂ t.density
  let A := fun i a => Matrix.fromBlocks (s.alice i a) 0 0 (t.alice i a)
  let B := fun j b => Matrix.fromBlocks (s.bob j b) 0 0 (t.bob j b)
  have hρ : ρ.PosSemidef := ((embeddedDensity_positive e₁ s.density_pos).smul hu).add
    ((embeddedDensity_positive e₂ t.density_pos).smul hv)
  have htr : ρ.trace=1 := by
    simp only [ρ,Matrix.trace_add,Matrix.trace_smul,embeddedDensity_trace e₁ he₁,
      embeddedDensity_trace e₂ he₂,s.density_trace,t.density_trace]
    simpa [Complex.real_smul,← Complex.ofReal_add] using congrArg (fun x : ℝ => (x : ℂ)) huv
  have hr := Scenarios.strategy_of_indexed_matrices (u • p+v • q) ρ hρ htr A B
    (fun i a => block_pair_positive (s.alice_pos i a) (t.alice_pos i a))
    (fun i => block_pair_sum _ _ (s.alice_sum i) (t.alice_sum i))
    (fun j b => block_pair_positive (s.bob_pos j b) (t.bob_pos j b))
    (fun j => block_pair_sum _ _ (s.bob_sum j) (t.bob_sum j))
  have hprob : ∀ i j a b, ((u • p+v • q) (i,j,a,b) : ℂ)=(ρ*(A i a ⊗ₖ B j b)).trace := by
    intro i j a b
    have hc₁ : (A i a ⊗ₖ B j b).submatrix e₁ e₁=s.alice i a ⊗ₖ s.bob j b := by ext x y;rfl
    have hc₂ : (A i a ⊗ₖ B j b).submatrix e₂ e₂=t.alice i a ⊗ₖ t.bob j b := by ext x y;rfl
    rw [show ρ=u • embeddedDensity e₁ s.density+v • embeddedDensity e₂ t.density from rfl,
      add_mul,smul_mul_assoc,smul_mul_assoc,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
      embeddedDensity_expectation,embeddedDensity_expectation,hc₁,hc₂,← hp,← hq]
    simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul]
  have h := hr hprob
  have hca : Fintype.card (Fin a₁ ⊕ Fin a₂)=a₁+a₂ := by simp
  have hcb : Fintype.card (Fin b₁ ⊕ Fin b₂)=b₁+b₂ := by simp
  rw [hca,hcb] at h
  exact h

theorem cq_convex (nA nB mA mB : ℕ) : Convex ℝ (Scenarios.Cq nA nB mA mB) := by
  rintro p ⟨a₁,b₁,s,hp⟩ q ⟨a₂,b₂,t,hq⟩ u v hu hv huv
  obtain ⟨r,hr⟩ := convex_pair_strategy s t hp hq hu hv huv
  exact ⟨a₁+a₂,b₁+b₂,r,hr⟩

theorem convex_pair_bounded {nA nB mA mB D E : ℕ} {p q : Scenarios.Behavior nA nB mA mB}
    (hp : p ∈ Scenarios.BoundedDimensionSet nA nB mA mB D)
    (hq : q ∈ Scenarios.BoundedDimensionSet nA nB mA mB E)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v=1) :
    u • p+v • q ∈ Scenarios.BoundedDimensionSet nA nB mA mB (D+E) := by
  obtain ⟨a₁,b₁,ha₁,hb₁,s,hs⟩ := hp
  obtain ⟨a₂,b₂,ha₂,hb₂,t,ht⟩ := hq
  obtain ⟨r,hr⟩ := convex_pair_strategy s t hs ht hu hv huv
  exact ⟨a₁+a₂,b₁+b₂,by omega,by omega,r,hr⟩

end QuantumBehaviors.SmallInputs
