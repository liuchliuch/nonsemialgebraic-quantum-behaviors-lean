import QuantumBehaviors.Scenarios.Operations

/-! Adding and merging inputs/outcomes preserves the actual finite density/POVM model. -/
namespace QuantumBehaviors.Scenarios

open Matrix
open scoped BigOperators Kronecker ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def matrixBorn (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ →ₗ[ℂ] ℂ where
  toFun A := {
    toFun := fun B => (ρ * (A ⊗ₖ B)).trace
    map_add' := fun B C => by simp [Matrix.kronecker_add, mul_add]
    map_smul' := fun c B => by simp [Matrix.kronecker_smul, mul_smul_comm] }
  map_add' A B := by ext C; simp [Matrix.add_kronecker, mul_add]
  map_smul' c A := by ext B; simp [Matrix.smul_kronecker, mul_smul_comm]

@[simp] theorem matrixBorn_apply (ρ : Matrix (ι × κ) (ι × κ) ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : matrixBorn ρ A B = (ρ * (A ⊗ₖ B)).trace := rfl

lemma complement_positive_of_sum_one {m : ℕ} (hm : 2 ≤ m) (A : Fin m → Matrix ι ι ℂ)
    (hA : ∀ a, (A a).PosSemidef) (hsum : ∑ a, A a = 1) :
    (1 - A (outcomeOne hm)).PosSemidef := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) A (Finset.mem_univ (outcomeOne hm))
  rw [hsum] at h
  have heq : (1 : Matrix ι ι ℂ) - A (outcomeOne hm) =
      ∑ a ∈ (Finset.univ : Finset (Fin m)).erase (outcomeOne hm), A a :=
    (eq_sub_iff_add_eq.mpr h).symm
  rw [heq]
  exact Matrix.posSemidef_sum _ fun a ha => hA a

lemma pad_effect_positive {m : ℕ} (hm : 2 ≤ m) (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (hE0 : (1 - E).PosSemidef) (a : Fin m) :
    (padBinary hm (effect E) a).PosSemidef := by
  unfold padBinary
  split_ifs
  · exact hE0
  · exact hE
  · exact Matrix.PosSemidef.zero

variable {nA nB mA mB : ℕ}

lemma extend_complex_entry (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (p : QuantumBehaviors.Behavior)
    (i : Fin nA) (j : Fin nB) (a : Fin mA) (b : Fin mB) :
    (extend hmA hmB p (i, j, a, b) : ℂ) =
      padBinary hmA (fun x => padBinary hmB
        (fun y => (p (extendInput i, extendInput j, x, y) : ℂ)) b) a := by
  dsimp only [extend]
  unfold padBinary
  split_ifs <;> simp

lemma retract_complex_entry (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB)
    (p : Behavior nA nB mA mB) (i j : Input) (a b : Bool) :
    (retract hnA hnB hmA hmB p (i, j, a, b) : ℂ) =
      mergeBinary hmA (fun x => mergeBinary hmB
        (fun y => (p (originalInput hnA i, originalInput hnB j, x, y) : ℂ)) b) a := by
  cases a <;> cases b <;>
    simp [retract, mergeBinary, Complex.ofReal_sum, Complex.ofReal_sub]

theorem extend_cq (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (extend (nA := nA) (nB := nB) hmA hmB) QuantumBehaviors.Cq (Cq nA nB mA mB) := by
  rintro p ⟨dA, dB, s, hs⟩
  let t : FiniteStrategy nA nB mA mB dA dB := {
    density := s.density
    density_pos := s.density_pos
    density_trace := s.density_trace
    alice := fun i => padBinary hmA (effect (s.alice (extendInput i)))
    bob := fun j => padBinary hmB (effect (s.bob (extendInput j)))
    alice_pos := fun i a => pad_effect_positive hmA _ (s.alice_pos _) (s.alice_complement_pos _) a
    alice_sum := fun i => pad_effect_sum hmA _
    bob_pos := fun j b => pad_effect_positive hmB _ (s.bob_pos _) (s.bob_complement_pos _) b
    bob_sum := fun j => pad_effect_sum hmB _ }
  refine ⟨dA, dB, t, ?_⟩
  intro i j a b
  rw [extend_complex_entry]
  change _ = matrixBorn s.density (padBinary hmA (effect (s.alice (extendInput i))) a)
    (padBinary hmB (effect (s.bob (extendInput j))) b)
  rw [pad_bilinear]
  congr 1
  funext x
  congr 1
  funext y
  exact hs _ _ x y

theorem retract_cq (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (retract hnA hnB hmA hmB) (Cq nA nB mA mB) QuantumBehaviors.Cq := by
  rintro p ⟨dA, dB, s, hs⟩
  let A := fun i : Input => s.alice (originalInput hnA i) (outcomeOne hmA)
  let B := fun j : Input => s.bob (originalInput hnB j) (outcomeOne hmB)
  let t : QuantumBehaviors.FiniteStrategy dA dB := {
    density := s.density
    density_pos := s.density_pos
    density_trace := s.density_trace
    alice := A
    bob := B
    alice_pos := fun i => s.alice_pos _ _
    alice_complement_pos := fun i => complement_positive_of_sum_one hmA _
      (s.alice_pos _) (s.alice_sum _)
    bob_pos := fun j => s.bob_pos _ _
    bob_complement_pos := fun j => complement_positive_of_sum_one hmB _
      (s.bob_pos _) (s.bob_sum _) }
  refine ⟨dA, dB, t, ?_⟩
  intro i j a b
  rw [retract_complex_entry]
  simp only [FiniteStrategy.realizes] at hs
  simp_rw [hs]
  change mergeBinary hmA (fun x => mergeBinary hmB
    (fun y => matrixBorn s.density (s.alice (originalInput hnA i) x)
      (s.bob (originalInput hnB j) y)) b) a = _
  rw [merge_bilinear, merge_binary_effect hmA _ (s.alice_sum _),
    merge_binary_effect hmB _ (s.bob_sum _)]
  rfl

theorem extend_cqa (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (extend (nA := nA) (nB := nB) hmA hmB) QuantumBehaviors.Cqa (Cqa nA nB mA mB) :=
  (extend_cq hmA hmB).closure (continuous_extend hmA hmB)

theorem retract_cqa (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (retract hnA hnB hmA hmB) (Cqa nA nB mA mB) QuantumBehaviors.Cqa :=
  (retract_cq hnA hnB hmA hmB).closure (continuous_retract hnA hnB hmA hmB)

end QuantumBehaviors.Scenarios
