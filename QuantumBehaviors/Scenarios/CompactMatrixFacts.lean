import QuantumBehaviors.ComplexSemidefinite
import Mathlib.Topology.Instances.Matrix

/-! Entry bounds and closedness of finite PSD constraints in the ordinary coordinate topology. -/
namespace QuantumBehaviors.Scenarios
open Matrix Set
open scoped BigOperators ComplexOrder
variable {J : Type*} [Fintype J] [DecidableEq J]

namespace PSDVectors

def Space (M : Matrix J J ℂ) (_ : M.PosSemidef) := J → ℂ
noncomputable instance (M : Matrix J J ℂ) (hM : M.PosSemidef) : AddCommGroup (Space M hM) :=
  inferInstanceAs (AddCommGroup (J → ℂ))
noncomputable instance (M : Matrix J J ℂ) (hM : M.PosSemidef) : Module ℂ (Space M hM) :=
  inferInstanceAs (Module ℂ (J → ℂ))
noncomputable instance (M : Matrix J J ℂ) (hM : M.PosSemidef) : SeminormedAddCommGroup (Space M hM) :=
  M.toSeminormedAddCommGroup hM
noncomputable instance (M : Matrix J J ℂ) (hM : M.PosSemidef) : InnerProductSpace ℂ (Space M hM) :=
  M.toInnerProductSpace hM

end PSDVectors

lemma psd_entry_norm_le_one {M : Matrix J J ℂ} (hM : M.PosSemidef)
    (hd : ∀ i, (M i i).re ≤ 1) (i j : J) : ‖M i j‖ ≤ 1 := by
  let e : J → PSDVectors.Space M hM := fun r => Pi.single r 1
  have hi (r s : J) : inner ℂ (e r) (e s)=M r s := by
    change (M *ᵥ (Pi.single s (1 : ℂ) : J → ℂ)) ⬝ᵥ star (Pi.single r (1 : ℂ) : J → ℂ)=M r s
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  have hn (r : J) : ‖e r‖ ≤ 1 := by
    have he : ‖e r‖^2=(M r r).re := by rw [norm_sq_eq_re_inner (𝕜 := ℂ),hi];rfl
    have hp := norm_nonneg (e r)
    nlinarith [hd r]
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul (hn i) (hn j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

lemma psd_trace_one_entry_bound {M : Matrix J J ℂ} (hM : M.PosSemidef) (htr : M.trace=1)
    (i j : J) : ‖M i j‖ ≤ 1 := by
  apply psd_entry_norm_le_one hM _ i j
  intro k
  have ht := congrArg Complex.re htr
  change Complex.reAddGroupHom (∑ r, M r r)=1 at ht
  rw [map_sum] at ht
  rw [← ht]
  exact Finset.single_le_sum (fun r hr => (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := r))).1) (Finset.mem_univ k)

lemma povm_entry_bound {K : Type*} [Fintype K] (M : K → Matrix J J ℂ)
    (hM : ∀ a, (M a).PosSemidef) (hs : ∑ a, M a=1) (a : K) (i j : J) : ‖M a i j‖ ≤ 1 := by
  apply psd_entry_norm_le_one (hM a) _ i j
  intro k
  have ht := congrArg (fun P : Matrix J J ℂ => (P k k).re) hs
  simp only [Matrix.sum_apply,Matrix.one_apply_eq,Complex.one_re] at ht
  change Complex.reAddGroupHom (∑ c, M c k k)=1 at ht
  rw [map_sum] at ht
  rw [← ht]
  exact Finset.single_le_sum (fun b hb => (RCLike.nonneg_iff.mp ((hM b).diag_nonneg (i := k))).1) (Finset.mem_univ a)

lemma isClosed_psd : IsClosed {M : Matrix J J ℂ | M.PosSemidef} := by
  have hself : IsClosed {M : Matrix J J ℂ | M.conjTranspose=M} := isClosed_eq (by fun_prop) continuous_id
  have hquad (v : J →₀ ℂ) : IsClosed {M : Matrix J J ℂ | 0 ≤ v.sum (fun i vi => v.sum (fun j vj => star vi*M i j*vj))} := by
    apply isClosed_le continuous_const
    dsimp only [Finsupp.sum]
    fun_prop
  have h := hself.inter (isClosed_iInter hquad)
  simpa only [Set.iInter_setOf,Set.mem_setOf_eq,Set.setOf_and,Matrix.PosSemidef,Matrix.IsHermitian] using h

end QuantumBehaviors.Scenarios
