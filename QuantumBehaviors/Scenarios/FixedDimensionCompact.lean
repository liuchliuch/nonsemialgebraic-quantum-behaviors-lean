import QuantumBehaviors.Scenarios.FixedDimension
import QuantumBehaviors.Scenarios.CompactMatrixFacts
import QuantumBehaviors.StateGNS

/-! Compactness of genuine fixed-size matrix strategies and their behavior image. -/
namespace QuantumBehaviors.Scenarios
open Matrix Set
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {nA nB mA mB dA dB : ℕ}

noncomputable def ValidParameters (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) : Prop :=
  (parameterDensity z).PosSemidef ∧ (parameterDensity z).trace=1 ∧
  (∀ i a, (parameterAlice z i a).PosSemidef) ∧ (∀ i, ∑ a, parameterAlice z i a=1) ∧
  (∀ j b, (parameterBob z j b).PosSemidef) ∧ (∀ j, ∑ b, parameterBob z j b=1)

noncomputable def parameterBehavior (z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) :
    Behavior nA nB mA mB := fun x =>
  (parameterDensity z*(parameterAlice z x.1 x.2.2.1 ⊗ₖ parameterBob z x.2.1 x.2.2.2)).trace.re

lemma continuous_parameterDensity : Continuous (parameterDensity (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) := by
  unfold parameterDensity
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop
lemma continuous_parameterAlice (i : Fin nA) (a : Fin mA) :
    Continuous (fun z : Parameters (nB := nB) (mB := mB) (dA := dA) (dB := dB) => parameterAlice z i a) := by
  unfold parameterAlice
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop
lemma continuous_parameterBob (j : Fin nB) (b : Fin mB) :
    Continuous (fun z : Parameters (nA := nA) (mA := mA) (dA := dA) (dB := dB) => parameterBob z j b) := by
  unfold parameterBob
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

lemma continuous_parameterBehavior : Continuous (parameterBehavior (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)) := by
  apply continuous_pi
  rintro ⟨i,j,a,b⟩
  unfold parameterBehavior Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply,Matrix.kroneckerMap_apply,parameterDensity,parameterAlice,parameterBob,Complex.mk_eq_add_mul_I]
  fun_prop

lemma isClosed_validParameters : IsClosed {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | ValidParameters z} := by
  have hD := isClosed_psd.preimage (continuous_parameterDensity (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB))
  have ht : IsClosed {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | (parameterDensity z).trace=1} := by
    apply isClosed_eq _ continuous_const
    unfold Matrix.trace Matrix.diag parameterDensity
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  have hAP := isClosed_iInter (fun i : Fin nA => isClosed_iInter fun a : Fin mA =>
    isClosed_psd.preimage (continuous_parameterAlice (nB := nB) (mB := mB) (dA := dA) (dB := dB) i a))
  have hBP := isClosed_iInter (fun j : Fin nB => isClosed_iInter fun b : Fin mB =>
    isClosed_psd.preimage (continuous_parameterBob (nA := nA) (mA := mA) (dA := dA) (dB := dB) j b))
  have hAS (i : Fin nA) : IsClosed {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | ∑ a, parameterAlice z i a=1} :=
    isClosed_eq (continuous_finset_sum Finset.univ (fun a ha => continuous_parameterAlice i a)) continuous_const
  have hBS (j : Fin nB) : IsClosed {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | ∑ b, parameterBob z j b=1} :=
    isClosed_eq (continuous_finset_sum Finset.univ (fun b hb => continuous_parameterBob j b)) continuous_const
  simpa only [ValidParameters,Set.setOf_and,Set.setOf_forall] using
    hD.inter (ht.inter (hAP.inter ((isClosed_iInter hAS).inter (hBP.inter (isClosed_iInter hBS)))))

lemma validParameters_entry_bound {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB)}
    (hz : ValidParameters z) (v : StrategyCoordinate nA nB mA mB dA dB) : |z v| ≤ 1 := by
  have hparts (c : ℂ) (hc : ‖c‖ ≤ 1) : |c.re| ≤ 1 ∧ |c.im| ≤ 1 :=
    ⟨(Complex.abs_re_le_norm c).trans hc,(Complex.abs_im_le_norm c).trans hc⟩
  rcases v with ⟨r,s,b⟩ | (⟨i,a,r,s,b⟩ | ⟨j,a,r,s,b⟩)
  · have h := hparts _ (psd_trace_one_entry_bound hz.1 hz.2.1 r s)
    cases b
    · exact h.1
    · exact h.2
  · have h := hparts _ (povm_entry_bound (parameterAlice z i) (hz.2.2.1 i) (hz.2.2.2.1 i) a r s)
    cases b
    · exact h.1
    · exact h.2
  · have h := hparts _ (povm_entry_bound (parameterBob z j) (hz.2.2.2.2.1 j) (hz.2.2.2.2.2 j) a r s)
    cases b
    · exact h.1
    · exact h.2

lemma isCompact_validParameters : IsCompact {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | ValidParameters z} := by
  apply (isCompact_Icc (a := fun _ : StrategyCoordinate nA nB mA mB dA dB => (-1 : ℝ))
    (b := fun _ => (1 : ℝ))).of_isClosed_subset isClosed_validParameters
  intro z hz
  constructor <;> intro v
  · exact (abs_le.mp (validParameters_entry_bound hz v)).1
  · exact (abs_le.mp (validParameters_entry_bound hz v)).2

lemma fixedDimension_eq_parameter_image : FixedDimensionSet nA nB mA mB dA dB =
    parameterBehavior '' {z : Parameters (nA := nA) (nB := nB) (mA := mA) (mB := mB) (dA := dA) (dB := dB) | ValidParameters z} := by
  ext p
  rw [fixed_dimension_parameters]
  constructor
  · rintro ⟨z,hD,htr,hA,hAs,hB,hBs,hreal⟩
    refine ⟨z,⟨hD,htr,hA,hAs,hB,hBs⟩,?_⟩
    funext ⟨i,j,a,b⟩
    exact (congrArg Complex.re (hreal i j a b)).symm
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z,hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2,?_⟩
    intro i j a b
    have hn := (densityFunctional (parameterDensity z) hz.1).map_nonneg
      (((hz.2.2.1 i a).kronecker (hz.2.2.2.2.1 j b)).nonneg)
    apply Complex.ext
    · rfl
    · exact (RCLike.nonneg_iff.mp hn).2.symm

theorem fixed_dimension_compact (nA nB mA mB dA dB : ℕ) :
    IsCompact (FixedDimensionSet nA nB mA mB dA dB) := by
  rw [fixedDimension_eq_parameter_image]
  exact isCompact_validParameters.image continuous_parameterBehavior

end QuantumBehaviors.Scenarios
