import QuantumBehaviors.SmallInputs.OptimizerReduction

/-! Exact input repetition and deletion, including the empty scenario. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators ComplexOrder

variable {n N : ℕ}

def pullInputs (f : Fin N → Fin n) (p : Scenarios.Behavior n n 2 2) : Scenarios.Behavior N N 2 2 :=
  fun ⟨i,j,a,b⟩ => p (f i,f j,a,b)

lemma pullInputs_continuous (f : Fin N → Fin n) : Continuous (pullInputs f) :=
  continuous_pi fun x => continuous_apply _

lemma pullInputs_cq (f : Fin N → Fin n) : Set.MapsTo (pullInputs f) (Scenarios.Cq n n 2 2) (Scenarios.Cq N N 2 2) := by
  rintro p ⟨dA,dB,s,hr⟩
  let t : Scenarios.FiniteStrategy N N 2 2 dA dB := {
    density := s.density
    density_pos := s.density_pos
    density_trace := s.density_trace
    alice := fun i => s.alice (f i)
    bob := fun j => s.bob (f j)
    alice_pos := fun i a => s.alice_pos (f i) a
    alice_sum := fun i => s.alice_sum (f i)
    bob_pos := fun j b => s.bob_pos (f j) b
    bob_sum := fun j => s.bob_sum (f j) }
  exact ⟨dA,dB,t,fun i j a b => hr (f i) (f j) a b⟩

lemma pullInputs_cqa (f : Fin N → Fin n) :
    Set.MapsTo (pullInputs f) (Scenarios.Cqa n n 2 2) (Scenarios.Cqa N N 2 2) :=
  (pullInputs_cq f).closure (pullInputs_continuous f)

lemma pullInputs_cqc (f : Fin N → Fin n) :
    Set.MapsTo (pullInputs f) (Scenarios.Cqc n n 2 2) (Scenarios.Cqc N N 2 2) := by
  rintro p ⟨H,hN,hI,hC,s,hr⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let t : Scenarios.CommutingStrategy N N 2 2 H := {
    state := s.state
    state_norm := s.state_norm
    alice := fun i => s.alice (f i)
    bob := fun j => s.bob (f j)
    alice_projection := fun i a => s.alice_projection (f i) a
    alice_sum := fun i => s.alice_sum (f i)
    bob_projection := fun j b => s.bob_projection (f j) b
    bob_sum := fun j => s.bob_sum (f j)
    cross_commute := fun i j a b => s.cross_commute (f i) (f j) a b }
  exact ⟨H,inferInstance,inferInstance,inferInstance,t,fun i j a b => hr (f i) (f j) a b⟩

lemma pullInputs_quantum (f : Fin N → Fin n) (t : Model) :
    Set.MapsTo (pullInputs f) (Scenarios.quantumSet n n 2 2 t) (Scenarios.quantumSet N N 2 2 t) := by
  cases t
  · exact pullInputs_cq f
  · exact pullInputs_cqa f
  · exact pullInputs_cqc f

lemma pullInputs_synchronous (f : Fin N → Fin n) {p : Scenarios.Behavior n n 2 2}
    (hp : Scenarios.Synchronous p) : Scenarios.Synchronous (pullInputs f p) :=
  fun i a b hab => hp (f i) a b hab

lemma pullInputs_synchronousSet (f : Fin N → Fin n) (t : Model) :
    Set.MapsTo (pullInputs f) (Scenarios.synchronousSet n t) (Scenarios.synchronousSet N t) :=
  fun _ hp => ⟨pullInputs_quantum f t hp.1,pullInputs_synchronous f hp.2⟩

lemma pullInputs_semialgebraic_preimage (f : Fin N → Fin n)
    {C : Set (Scenarios.Behavior N N 2 2)} (hC : IsSemialgebraic C) :
    IsSemialgebraic (pullInputs f ⁻¹' C) := by
  have he := hC.polynomial_preimage (fun x : Scenarios.Coordinate N N 2 2 =>
    MvPolynomial.X (f x.1,f x.2.1,x.2.2.1,x.2.2.2))
  simpa only [MvPolynomial.eval_X] using he

def padToThree (hn : 0 < n) (i : Fin 3) : Fin n :=
  if hi : i.val < n then ⟨i.val,hi⟩ else ⟨0,hn⟩

@[simp] lemma padToThree_cast (hn : 0 < n) (hn3 : n ≤ 3) (i : Fin n) :
    padToThree hn (Fin.castLE hn3 i) = i := by
  apply Fin.ext
  simp only [padToThree, Fin.val_castLE, i.isLt, ↓reduceDIte]

lemma pullInputs_retract_pad (hn : 0 < n) (hn3 : n ≤ 3) (p : Scenarios.Behavior n n 2 2) :
    pullInputs (Fin.castLE hn3) (pullInputs (padToThree hn) p) = p := by
  funext x
  rcases x with ⟨i,j,a,b⟩
  simp only [pullInputs, padToThree_cast]

lemma small_synchronous_preimage (hn : 0 < n) (hn3 : n ≤ 3) (t : Model) :
    Scenarios.synchronousSet n t = pullInputs (padToThree hn) ⁻¹' Scenarios.synchronousSet 3 t := by
  ext p
  constructor
  · intro hp
    exact pullInputs_synchronousSet (padToThree hn) t hp
  · intro hp
    have he := pullInputs_synchronousSet (Fin.castLE hn3) t hp
    simpa only [pullInputs_retract_pad] using he

/-- All positive input counts at most three reduce exactly to the three-input set. -/
theorem small_synchronous_semialgebraic_of_three (hn : 0 < n) (hn3 : n ≤ 3) (t : Model)
    (h3 : IsSemialgebraic (Scenarios.synchronousSet 3 t)) :
    IsSemialgebraic (Scenarios.synchronousSet n t) := by
  rw [small_synchronous_preimage hn hn3 t]
  exact pullInputs_semialgebraic_preimage _ h3

lemma empty_behavior_mem_cq (p : Scenarios.Behavior 0 0 2 2) : p ∈ Scenarios.Cq 0 0 2 2 := by
  let s : Scenarios.FiniteStrategy 0 0 2 2 1 1 := {
    density := 1
    density_pos := Matrix.PosSemidef.one
    density_trace := by simp
    alice := Fin.elim0
    bob := Fin.elim0
    alice_pos := fun i => Fin.elim0 i
    alice_sum := fun i => Fin.elim0 i
    bob_pos := fun i => Fin.elim0 i
    bob_sum := fun i => Fin.elim0 i }
  exact ⟨1,1,s,fun i => Fin.elim0 i⟩

lemma empty_synchronousSet (t : Model) : Scenarios.synchronousSet 0 t = Set.univ := by
  ext p
  simp only [Set.mem_univ, iff_true]
  have hq := empty_behavior_mem_cq p
  refine ⟨?_,fun i => Fin.elim0 i⟩
  cases t
  · exact hq
  · exact subset_closure hq
  · exact Scenarios.binary_cq_subset_cqc 0 0 hq

lemma empty_synchronous_semialgebraic (t : Model) : IsSemialgebraic (Scenarios.synchronousSet 0 t) := by
  rw [empty_synchronousSet]
  exact IsSemialgebraic.univ

end QuantumBehaviors.SmallInputs
