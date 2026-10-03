import QuantumBehaviors.NPA.FiniteGram
import QuantumBehaviors.NPA.InfiniteRepresentation
import QuantumBehaviors.Ultralimit

/-! Bounded finite Gram vectors give an actual Hilbert ultralimit and a complete NPA representation. -/
namespace QuantumBehaviors.NPA
open Filter UniformSpace
open scoped Topology ENNReal

abbrev FiniteWordSpace (n : ℕ) := EuclideanSpace ℂ (BoundedWord (n+1))
variable {p : Behavior} (c : ∀ n, Certificate n p)

noncomputable def vectorAt (w : Word) (n : ℕ) : FiniteWordSpace n :=
  if h : w.length ≤ n+1 then gramVector (c n).gram ⟨w,h⟩ else 0

lemma vectorAt_of_le (w : Word) (n : ℕ) (h : w.length ≤ n+1) :
    vectorAt c w n=gramVector (c n).gram ⟨w,h⟩ := by simp [vectorAt,h]

@[simp] lemma vectorAt_empty (n : ℕ) : vectorAt c [] n=gramVector (c n).gram (emptyIndex n) := by
  simp [vectorAt,emptyIndex]
@[simp] lemma vectorAt_singleton (a : Letter) (n : ℕ) :
    vectorAt c [a] n=gramVector (c n).gram (letterIndex n a) := by simp [vectorAt,letterIndex]

lemma vectorAt_norm_le_one (w : Word) (n : ℕ) : ‖vectorAt c w n‖ ≤ 1 := by
  unfold vectorAt
  split_ifs with h
  · exact (c n).gramVector_norm_le_one _
  · simp

variable (U : Ultrafilter ℕ)
noncomputable def wordPre (w : Word) : HilbertUltralimit.PreHilbert FiniteWordSpace U :=
  (HilbertUltralimit.toBounded FiniteWordSpace U).symm
    ⟨vectorAt c w,memℓp_infty ⟨1,by rintro r ⟨n,rfl⟩;exact vectorAt_norm_le_one c w n⟩⟩

noncomputable def wordVector (w : Word) : HilbertUltralimit.Space FiniteWordSpace U :=
  (wordPre c U w : HilbertUltralimit.Space FiniteWordSpace U)

lemma word_inner_tendsto (u v : Word) :
    Tendsto (fun n => inner ℂ (vectorAt c u n) (vectorAt c v n)) U
      (𝓝 (inner ℂ (wordVector c U u) (wordVector c U v))) := by
  rw [wordVector,wordVector,HilbertUltralimit.inner_completion_coe]
  exact HilbertUltralimit.tendsto_inner FiniteWordSpace U (wordPre c U u) (wordPre c U v)

lemma wordVector_normalized : inner ℂ (wordVector c U []) (wordVector c U [])=1 := by
  have heq : (fun n => inner ℂ (vectorAt c [] n) (vectorAt c [] n))=fun _ : ℕ => (1 : ℂ) := by
    funext n
    rw [vectorAt_empty,gramVector_inner (c n).positive,(c n).normalized]
  have h := word_inner_tendsto c U [] []
  rw [heq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma wordVector_relations (hU : (U : Filter ℕ) ≤ atTop) (u v r s : Word)
    (hrel : WordRel (u.reverse++v) (r.reverse++s)) :
    inner ℂ (wordVector c U u) (wordVector c U v)=inner ℂ (wordVector c U r) (wordVector c U s) := by
  have heq : (fun n => inner ℂ (vectorAt c u n) (vectorAt c v n)) =ᶠ[U]
      (fun n => inner ℂ (vectorAt c r n) (vectorAt c s n)) := by
    filter_upwards [(eventually_ge_atTop (u.length+v.length+r.length+s.length)).filter_mono hU] with n hn
    have hu : u.length ≤ n+1 := by omega
    have hv : v.length ≤ n+1 := by omega
    have hr : r.length ≤ n+1 := by omega
    have hs : s.length ≤ n+1 := by omega
    rw [vectorAt_of_le c u n hu,vectorAt_of_le c v n hv,vectorAt_of_le c r n hr,vectorAt_of_le c s n hs,
      gramVector_inner (c n).positive,gramVector_inner (c n).positive]
    exact (c n).relations _ _ _ _ hrel
  exact tendsto_nhds_unique (word_inner_tendsto c U u v)
    ((word_inner_tendsto c U r s).congr' heq.symm)

lemma vectorAt_born (n : ℕ) (i j : Input) (a b : Bool) :
    (p (i,j,a,b) : ℂ)=vectorBorn (fun w => vectorAt c w n) i j a b := by
  cases a <;> cases b <;>
    simpa only [vectorBorn,bornValue,Bool.false_eq_true,↓reduceIte,vectorAt_empty,vectorAt_singleton,
      gramVector_inner (c n).positive] using (c n).born i j _ _

lemma wordVector_born (i j : Input) (a b : Bool) :
    (p (i,j,a,b) : ℂ)=vectorBorn (wordVector c U) i j a b := by
  have hA := word_inner_tendsto c U [] [Sum.inl i]
  have hB := word_inner_tendsto c U [] [Sum.inr j]
  have hJ := word_inner_tendsto c U [Sum.inl i] [Sum.inr j]
  have hlim : Tendsto (fun n => vectorBorn (fun w => vectorAt c w n) i j a b) U
      (𝓝 (vectorBorn (wordVector c U) i j a b)) := by
    cases a <;> cases b <;> simp only [vectorBorn,Bool.false_eq_true,↓reduceIte]
    · exact ((tendsto_const_nhds.sub hA).sub hB).add hJ
    · exact hB.sub hJ
    · exact hA.sub hJ
    · exact hJ
  have heq : (fun n => vectorBorn (fun w => vectorAt c w n) i j a b)=fun _ : ℕ => (p (i,j,a,b) : ℂ) := by
    funext n
    exact (vectorAt_born c n i j a b).symm
  rw [heq] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

noncomputable def representationOfCertificates (hU : (U : Filter ℕ) ≤ atTop) :
    GramRepresentation p (HilbertUltralimit.Space FiniteWordSpace U) where
  vector := wordVector c U
  normalized := wordVector_normalized c U
  relations := wordVector_relations c U hU
  born := wordVector_born c U

/-- NPA completeness: all finite levels produce actual projections on an actual complete Hilbert space. -/
theorem mem_cqc_of_all_levels {p : Behavior} (hp : ∀ k, p ∈ level k) : p ∈ Cqc := by
  classical
  let c : ∀ n, Certificate n p := fun n => Classical.choice (hp n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  exact (representationOfCertificates c U (Ultrafilter.of_le atTop)).mem_cqc

theorem complete_hierarchy : (⋂ k : ℕ, level k)=Cqc := by
  ext p
  simp only [Set.mem_iInter]
  exact ⟨mem_cqc_of_all_levels,fun hp k => cqc_subset_level k hp⟩

theorem excluded_at_finite_level {p : Behavior} (hp : p ∉ Cqc) : ∃ k, p ∉ level k := by
  by_contra h
  push_neg at h
  exact hp (mem_cqc_of_all_levels h)

end QuantumBehaviors.NPA
