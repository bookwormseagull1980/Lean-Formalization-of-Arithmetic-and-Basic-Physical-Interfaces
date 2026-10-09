module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic.Ring

/-!
# The closure of a symmetric operator with a complete real eigenbasis

All operators act on the original Hilbert space. Testing the actual adjoint
against the basis determines its coefficients. Finite sums of eigenvectors
then converge in the graph, identifying the closure of the original operator
with its adjoint and establishing the uniqueness of its self-adjoint extension.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate LinearPMap
open Filter

namespace GeneratedFoundations.Operations.EigenbasisClosure

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

variable (B : HilbertBasis ι ℂ E) (T : E →ₗ.[ℂ] E) (eigenvalue : ι → ℝ)
  (hmem : ∀ i, B i ∈ T.domain)
  (heigen : ∀ i, T ⟨B i, hmem i⟩ = (eigenvalue i : ℂ) • B i)

include hmem in
omit [CompleteSpace E] in
theorem domain_dense : Dense (T.domain : Set E) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← B.dense_span]
  apply Submodule.topologicalClosure_mono
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)

omit [CompleteSpace E] in
/-- Equality of all coefficients is equality of the original Hilbert vectors. -/
theorem eq_of_coefficients {x y : E}
    (h : ∀ i, inner ℂ (B i) x = inner ℂ (B i) y) : x = y := by
  apply B.repr.injective
  apply lp.ext
  funext i
  simpa only [B.repr_apply_apply] using h i

include hmem heigen in
theorem adjoint_coefficients (y : T.adjoint.domain) (i : ι) :
    inner ℂ (B i) (T.adjoint y) = (eigenvalue i : ℂ) * inner ℂ (B i) (y : E) := by
  have h := (LinearPMap.adjoint_isFormalAdjoint (domain_dense B T hmem)).symm
    ⟨B i, hmem i⟩ y
  rw [heigen i, inner_smul_left, Complex.conj_ofReal] at h
  exact h.symm

variable (hsym : T.IsFormalAdjoint T)

include hmem heigen hsym in
omit [CompleteSpace E] in
theorem operator_coefficients (x : T.domain) (i : ι) :
    inner ℂ (B i) (T x) = (eigenvalue i : ℂ) * inner ℂ (B i) (x : E) := by
  have h := hsym ⟨B i, hmem i⟩ x
  rw [heigen i, inner_smul_left, Complex.conj_ofReal] at h
  exact h.symm

include hmem heigen hsym in
theorem adjoint_domain_iff (y : E) :
    y ∈ T.adjoint.domain ↔
      ∃ z : E, ∀ i, inner ℂ (B i) z = (eigenvalue i : ℂ) * inner ℂ (B i) y := by
  constructor
  · intro hy
    exact ⟨T.adjoint ⟨y, hy⟩, adjoint_coefficients B T eigenvalue hmem heigen ⟨y, hy⟩⟩
  · rintro ⟨z, hz⟩
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨z, ?_⟩
    intro x
    rw [← B.tsum_inner_mul_inner z (x : E), ← B.tsum_inner_mul_inner y (T x)]
    apply tsum_congr
    intro i
    rw [← inner_conj_symm z (B i), hz i, map_mul, Complex.conj_ofReal,
      inner_conj_symm, operator_coefficients B T eigenvalue hmem heigen hsym x i]
    ring

include hmem heigen in
theorem adjoint_symmetric : T.adjoint.IsFormalAdjoint T.adjoint := by
  intro x y
  rw [← B.tsum_inner_mul_inner (T.adjoint x) (y : E),
    ← B.tsum_inner_mul_inner (x : E) (T.adjoint y)]
  apply tsum_congr
  intro i
  rw [← inner_conj_symm (T.adjoint x) (B i),
    adjoint_coefficients B T eigenvalue hmem heigen x i, map_mul, Complex.conj_ofReal,
    inner_conj_symm, adjoint_coefficients B T eigenvalue hmem heigen y i]
  ring

include hmem heigen hsym in
theorem adjoint_domain_iff_memℓp (y : E) :
    y ∈ T.adjoint.domain ↔ Memℓp (fun i => (eigenvalue i : ℂ) * inner ℂ (B i) y) 2 := by
  rw [adjoint_domain_iff B T eigenvalue hmem heigen hsym]
  constructor
  · rintro ⟨z, hz⟩
    convert lp.memℓp (B.repr z) using 1
    funext i
    exact (hz i).symm.trans (B.repr_apply_apply z i).symm
  · intro hy
    let c : lp (fun _ : ι => ℂ) 2 := ⟨fun i => (eigenvalue i : ℂ) * inner ℂ (B i) y, hy⟩
    refine ⟨B.repr.symm c, ?_⟩
    intro i
    rw [← B.repr_apply_apply, B.repr.apply_symm_apply]

include hmem heigen hsym in
/-- The full adjoint domain is the square-summable weighted coefficient domain. -/
theorem adjoint_domain_iff_summable (y : E) :
    y ∈ T.adjoint.domain ↔
      Summable (fun i => (eigenvalue i) ^ 2 * ‖inner ℂ (B i) y‖ ^ 2) := by
  rw [adjoint_domain_iff_memℓp B T eigenvalue hmem heigen hsym,
    memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

include hmem hsym in
theorem le_adjoint : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint (domain_dense B T hmem) hsym

include hmem heigen hsym in
theorem adjoint_selfAdjoint : IsSelfAdjoint T.adjoint := by
  have hle := le_adjoint B T hmem hsym
  have hm : ∀ i, B i ∈ T.adjoint.domain := fun i => hle.1 (hmem i)
  have he : ∀ i, T.adjoint ⟨B i, hm i⟩ = (eigenvalue i : ℂ) • B i := by
    intro i
    exact (hle.2 (x := ⟨B i, hmem i⟩) (y := ⟨B i, hm i⟩) rfl).symm.trans (heigen i)
  have hd := domain_dense B T.adjoint hm
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      exact (adjoint_domain_iff B T eigenvalue hmem heigen hsym y).mpr
        ⟨T.adjoint.adjoint ⟨y, hy⟩,
          adjoint_coefficients B T.adjoint eigenvalue hm he ⟨y, hy⟩⟩
    · intro x y hxy
      apply eq_of_coefficients B
      intro i
      rw [adjoint_coefficients B T.adjoint eigenvalue hm he x i,
        adjoint_coefficients B T eigenvalue hmem heigen y i, hxy]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint hd
      (adjoint_symmetric B T eigenvalue hmem heigen)

include hmem heigen in
/-- Finite sums of the original eigenvectors approximate every adjoint graph point. -/
theorem adjoint_graph_le_closure_graph :
    T.adjoint.graph ≤ T.graph.topologicalClosure := by
  intro p hp
  obtain ⟨x, rfl⟩ := (T.adjoint.mem_graph_iff').mp hp
  have hs := (B.hasSum_repr (x : E)).prodMk (B.hasSum_repr (T.adjoint x))
  apply mem_closure_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  have hi : (B.repr (x : E) i • B i,
      B.repr (T.adjoint x) i • B i) ∈ T.graph := by
    refine (T.mem_graph_iff').mpr ⟨⟨B.repr (x : E) i • B i,
      T.domain.smul_mem _ (hmem i)⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change T (B.repr (x : E) i • (⟨B i, hmem i⟩ : T.domain)) = _
      rw [LinearPMap.map_smul, heigen i, smul_smul]
      simp only [B.repr_apply_apply]
      rw [adjoint_coefficients B T eigenvalue hmem heigen x i]
      congr 1
      exact mul_comm _ _
  exact hi

include hmem heigen hsym in
theorem closure_eq_adjoint : T.closure = T.adjoint := by
  have hclosed := LinearPMap.adjoint_isClosed (domain_dense B T hmem)
  have hclosable := hclosed.isClosable.leIsClosable (le_adjoint B T hmem hsym)
  apply LinearPMap.eq_of_eq_graph
  rw [← hclosable.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact T.graph.topologicalClosure_minimal
      (LinearPMap.le_graph_of_le (le_adjoint B T hmem hsym)) hclosed
  · exact adjoint_graph_le_closure_graph B T eigenvalue hmem heigen

include hmem heigen hsym in
theorem closure_selfAdjoint : IsSelfAdjoint T.closure := by
  rw [closure_eq_adjoint B T eigenvalue hmem heigen hsym]
  exact adjoint_selfAdjoint B T eigenvalue hmem heigen hsym

include hmem heigen hsym in
/-- Uniqueness is among all self-adjoint extensions in the original Hilbert space. -/
theorem selfAdjoint_extension_unique (S : E →ₗ.[ℂ] E)
    (hS : IsSelfAdjoint S) (hTS : T ≤ S) : S = T.closure := by
  have hsS : S.IsFormalAdjoint S := by
    have h := LinearPMap.adjoint_isFormalAdjoint hS.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hS] at h
  have hformal : T.IsFormalAdjoint S := by
    intro x y
    let xS : S.domain := ⟨x, hTS.1 x.property⟩
    rw [hTS.2 (x := x) (y := xS) rfl]
    exact hsS xS y
  have hle : S ≤ T.adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint (domain_dense B T hmem) hformal
  have hc := (adjoint_selfAdjoint B T eigenvalue hmem heigen hsym).isClosed.isClosable
    |>.leIsClosable (le_adjoint B T hmem hsym)
  apply le_antisymm
  · rwa [closure_eq_adjoint B T eigenvalue hmem heigen hsym]
  · apply LinearPMap.le_of_le_graph
    rw [← hc.graph_closure_eq_closure_graph]
    exact T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hTS) hS.isClosed

end GeneratedFoundations.Operations.EigenbasisClosure
