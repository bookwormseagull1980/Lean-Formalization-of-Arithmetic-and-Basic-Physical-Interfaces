module

public import GeneratedFoundations.Operations.SourceCoherentObservations
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix

/-!
# The complete continuous algebra of coherent source processes

The group carries its actual matrix topology. Compactness is proved from
closed unitary and determinant equations and bounded matrix entries. The
generating continuous functions are the expectations of the previously
constructed preparations and bounded observables in the finite source algebra.
Their tomography identities separate processes, so the unital star algebra
they generate is uniformly dense in all continuous complex functions.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Operations.SourceCoherentObservations

namespace GeneratedFoundations.Operations.SourceProcessAlgebra

theorem specialUnitary_entry_bound (M : Mat2)
    (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 2) : ‖M i j‖ ≤ 1 := by
  have hn := specialUnitary_norms M hM
  have h0 : ‖M 0 0‖ ≤ 1 := by nlinarith [sq_nonneg ‖M 0 1‖, norm_nonneg (M 0 0)]
  have h1 : ‖M 0 1‖ ≤ 1 := by nlinarith [sq_nonneg ‖M 0 0‖, norm_nonneg (M 0 1)]
  have he := specialUnitary_entries M hM
  rw [he]
  fin_cases i <;> fin_cases j
  all_goals first | simpa [canonical] using h0 | simpa [canonical] using h1

theorem specialUnitary_closed :
    IsClosed (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set Mat2) := by
  have he : (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set Mat2) =
      (Matrix.unitaryGroup (Fin 2) ℂ : Set Mat2) ∩ {M : Mat2 | M.det = 1} := by
    ext M
    exact Matrix.mem_specialUnitaryGroup_iff
  rw [he]
  exact isClosed_unitary.inter (isClosed_eq (by fun_prop) continuous_const)

theorem specialUnitary_compact :
    IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set Mat2) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset specialUnitary_closed
  intro M hM
  change ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1
  intro i j
  exact mem_closedBall_zero_iff.mpr (specialUnitary_entry_bound M hM i j)

instance : CompactSpace SU2 := isCompact_iff_compactSpace.mp specialUnitary_compact

theorem xResponse_continuous {b : ℝ} (hb : 0 < b) (j k : Fin 2) :
    Continuous (xResponse hb j k) := by
  change Continuous (fun U : SU2 => xResponse hb j k U)
  simp_rw [xResponse_eq]
  exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp
    ((continuous_apply k).comp ((continuous_apply j).comp continuous_subtype_val)))

theorem yResponse_continuous {b : ℝ} (hb : 0 < b) (j k : Fin 2) :
    Continuous (yResponse hb j k) := by
  change Continuous (fun U : SU2 => yResponse hb j k U)
  simp_rw [yResponse_eq]
  exact Complex.continuous_ofReal.comp (Complex.continuous_im.comp
    ((continuous_apply k).comp ((continuous_apply j).comp continuous_subtype_val)))

def xResponseMap {b : ℝ} (hb : 0 < b) (j k : Fin 2) : C(SU2, ℂ) :=
  ⟨xResponse hb j k, xResponse_continuous hb j k⟩

def yResponseMap {b : ℝ} (hb : 0 < b) (j k : Fin 2) : C(SU2, ℂ) :=
  ⟨yResponse hb j k, yResponse_continuous hb j k⟩

def responseFamily {b : ℝ} (hb : 0 < b) : Set C(SU2, ℂ) :=
  Set.range (fun jk : Fin 2 × Fin 2 => xResponseMap hb jk.1 jk.2) ∪
    Set.range (fun jk : Fin 2 × Fin 2 => yResponseMap hb jk.1 jk.2)

def processAlgebra {b : ℝ} (hb : 0 < b) : StarSubalgebra ℂ C(SU2, ℂ) :=
  StarAlgebra.adjoin ℂ (responseFamily hb)

theorem xResponseMap_mem {b : ℝ} (hb : 0 < b) (j k : Fin 2) :
    xResponseMap hb j k ∈ processAlgebra hb :=
  StarAlgebra.subset_adjoin ℂ _ (Set.mem_union_left _ ⟨(j, k), rfl⟩)

theorem yResponseMap_mem {b : ℝ} (hb : 0 < b) (j k : Fin 2) :
    yResponseMap hb j k ∈ processAlgebra hb :=
  StarAlgebra.subset_adjoin ℂ _ (Set.mem_union_right _ ⟨(j, k), rfl⟩)

theorem processAlgebra_separates {b : ℝ} (hb : 0 < b) :
    (processAlgebra hb).SeparatesPoints := by
  intro U V hUV
  obtain ⟨j, k, h | h⟩ := responses_separate hb hUV
  · exact ⟨xResponse hb j k, ⟨xResponseMap hb j k, xResponseMap_mem hb j k, rfl⟩, h⟩
  · exact ⟨yResponse hb j k, ⟨yResponseMap hb j k, yResponseMap_mem hb j k, rfl⟩, h⟩

/-- Completion in the compact-domain supremum norm gives the full process algebra. -/
theorem processAlgebra_complete {b : ℝ} (hb : 0 < b) :
    (processAlgebra hb).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (processAlgebra hb) (processAlgebra_separates hb)

end GeneratedFoundations.Operations.SourceProcessAlgebra
