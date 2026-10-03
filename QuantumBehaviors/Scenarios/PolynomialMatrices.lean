import QuantumBehaviors.ComplexSemidefinite

/-! Genuine polynomial-coordinate descriptions of finite complex matrix expressions. -/
namespace QuantumBehaviors.Scenarios
open Matrix
open scoped BigOperators ComplexOrder

/-- A complex-valued polynomial function of finitely many real parameters. -/
def IsComplexPolynomial {V : Type*} (f : (V → ℝ) → ℂ) : Prop :=
  ∃ p q : MvPolynomial V ℝ, ∀ x, f x = ⟨MvPolynomial.eval x p,MvPolynomial.eval x q⟩

namespace IsComplexPolynomial
variable {V : Type*} {f g : (V → ℝ) → ℂ}

lemma const (c : ℂ) : IsComplexPolynomial (fun _ : V → ℝ => c) :=
  ⟨MvPolynomial.C c.re,MvPolynomial.C c.im,by intro x; simp⟩

lemma real_polynomial (p : MvPolynomial V ℝ) : IsComplexPolynomial (fun x => (MvPolynomial.eval x p : ℂ)) :=
  ⟨p,0,by intro x; simp; rfl⟩

lemma coord (v : V) : IsComplexPolynomial (fun x => (x v : ℂ)) := by
  simpa using real_polynomial (MvPolynomial.X v)

lemma complex_coord (r i : V) : IsComplexPolynomial (fun x => (⟨x r,x i⟩ : ℂ)) :=
  ⟨MvPolynomial.X r,MvPolynomial.X i,by simp⟩

lemma add (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) : IsComplexPolynomial (fun x => f x+g x) := by
  obtain ⟨p,q,hf⟩ := hf
  obtain ⟨r,s,hg⟩ := hg
  exact ⟨p+r,q+s,by intro x; dsimp only; rw [hf,hg]; simp; rfl⟩

lemma sub (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) : IsComplexPolynomial (fun x => f x-g x) := by
  obtain ⟨p,q,hf⟩ := hf
  obtain ⟨r,s,hg⟩ := hg
  exact ⟨p-r,q-s,by intro x; dsimp only; rw [hf,hg]; simp; rfl⟩

lemma mul (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) : IsComplexPolynomial (fun x => f x*g x) := by
  obtain ⟨p,q,hf⟩ := hf
  obtain ⟨r,s,hg⟩ := hg
  refine ⟨p*r-q*s,p*s+q*r,?_⟩
  intro x
  dsimp only
  rw [hf,hg]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

lemma sum {J : Type*} (s : Finset J) (f : J → (V → ℝ) → ℂ) (hf : ∀ j ∈ s, IsComplexPolynomial (f j)) :
    IsComplexPolynomial (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (V := V) 0
  | @insert j s hjs ih =>
      have h := (hf j (by simp)).add (ih (fun k hk => hf k (by simp [hk])))
      simpa only [Finset.sum_insert hjs] using h

lemma sum_fintype {J : Type*} [Fintype J] (f : J → (V → ℝ) → ℂ) (hf : ∀ j, IsComplexPolynomial (f j)) :
    IsComplexPolynomial (fun x => ∑ j, f j x) := sum Finset.univ f (fun j _ => hf j)

lemma eq_semialgebraic (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsSemialgebraic {x | f x = g x} := by
  obtain ⟨p,q,h⟩ := hf.sub hg
  have heq : {x | f x = g x} = {x | MvPolynomial.eval x p = 0} ∩ {x | MvPolynomial.eval x q = 0} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff]
    have hx := h x
    dsimp only at hx
    rw [← sub_eq_zero,hx]
    exact Complex.ext_iff
  rw [heq]
  exact (IsSemialgebraic.polynomial_zero p).inter (IsSemialgebraic.polynomial_zero q)

end IsComplexPolynomial

lemma polynomial_matrix_psd {V J : Type*} [Fintype J] [DecidableEq J]
    (M : (V → ℝ) → Matrix J J ℂ) (hM : ∀ i j, IsComplexPolynomial (fun x => M x i j)) :
    IsSemialgebraic {x | (M x).PosSemidef} := by
  classical
  choose p q hp using hM
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let poly : ComplexMatrixCoordinate (Fintype.card J) → MvPolynomial V ℝ :=
    fun c => if c.2.2 then q (e c.1) (e c.2.1) else p (e c.1) (e c.2.1)
  have h := (complex_psd_semialgebraic (Fintype.card J)).polynomial_preimage poly
  have heval (x : V → ℝ) : complexMatrix (fun c => MvPolynomial.eval x (poly c)) = (M x).submatrix e e := by
    ext i j
    exact (hp (e i) (e j) x).symm
  change IsSemialgebraic {x | (complexMatrix (fun c => MvPolynomial.eval x (poly c))).PosSemidef} at h
  have heq : {x | (complexMatrix (fun c => MvPolynomial.eval x (poly c))).PosSemidef} =
      {x | (M x).PosSemidef} := by
    ext x
    rw [Set.mem_setOf_eq,Set.mem_setOf_eq,heval]
    constructor
    · intro h
      have hh := h.submatrix e.symm
      simpa only [Matrix.submatrix_submatrix,Equiv.self_comp_symm,Matrix.submatrix_id_id] using hh
    · intro h
      exact h.submatrix e
  rwa [heq] at h

lemma polynomial_matrix_eq {V J K : Type*} [Fintype J] [Fintype K]
    (M N : (V → ℝ) → Matrix J K ℂ)
    (hM : ∀ i j, IsComplexPolynomial (fun x => M x i j))
    (hN : ∀ i j, IsComplexPolynomial (fun x => N x i j)) :
    IsSemialgebraic {x | M x = N x} := by
  have h := IsSemialgebraic.forall_finite (fun ij : J × K => {x | M x ij.1 ij.2 = N x ij.1 ij.2})
    (fun ij => (hM ij.1 ij.2).eq_semialgebraic (hN ij.1 ij.2))
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h ij => congrFun (congrFun h ij.1) ij.2,fun h => Matrix.ext fun i j => h (i,j)⟩

end QuantumBehaviors.Scenarios
