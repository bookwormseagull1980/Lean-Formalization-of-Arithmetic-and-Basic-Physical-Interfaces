module

public import GeneratedFoundations.Operations.SourceFiniteLadder
public import GeneratedFoundations.Operations.SourcePreparedResponse
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The algebra of a finite Gaussian compression

The selected Hermite states form an orthonormal basis of their subspace in
the Gaussian Hilbert space. Matrix coordinates give a star-algebra
equivalence with all linear endomorphisms of this subspace. Under this
equivalence the finite ladder matrix is the compressed differential
annihilator, and its generated star algebra is the full endomorphism algebra.
-/

@[expose] public section

noncomputable section

open Module
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.GaussianAffineLadder (embedding)
open GeneratedFoundations.Operations.HermiteFamily

namespace GeneratedFoundations.Operations.SourceFiniteCornerAlgebra

open FiniteLadderAlgebra (Index Mat lowering)

variable {b : ℝ} (hb : 0 < b) (n : ℕ)

abbrev Carrier := FiniteHermiteCorner.sourceSpace hb (fun i : Index n => i.val)

instance carrier_finiteDimensional : FiniteDimensional ℂ (Carrier hb n) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range (fun i : Index n => state hb i.val))

def sourceBasis : OrthonormalBasis (Index n) ℂ (Carrier hb n) :=
  (Basis.span ((state_orthonormal hb).comp (fun i : Index n => i.val)
    Fin.val_injective).linearIndependent).toOrthonormalBasis (by
      apply orthonormal_iff_ite.mpr
      intro i j
      change inner ℂ
        ((Basis.span ((state_orthonormal hb).comp (fun i : Index n => i.val)
          Fin.val_injective).linearIndependent i : Carrier hb n) : ComplexL2)
        ((Basis.span ((state_orthonormal hb).comp (fun i : Index n => i.val)
          Fin.val_injective).linearIndependent j : Carrier hb n) : ComplexL2) = _
      simp only [Basis.coe_span_apply, Function.comp_apply,
        SourceMatrixUnits.state_inner, Fin.val_inj])

@[simp] theorem sourceBasis_coe (i : Index n) :
    (sourceBasis hb n i : ComplexL2) = state hb i.val := by
  have h : sourceBasis hb n i =
      Basis.span ((state_orthonormal hb).comp (fun i : Index n => i.val)
        Fin.val_injective).linearIndependent i :=
    congrFun (Basis.coe_toOrthonormalBasis
      (E := Submodule.span ℂ (Set.range (state hb ∘ fun i : Index n => i.val))) _ _) i
  exact (congrArg Subtype.val h).trans (Basis.coe_span_apply _ i)

def matrixEquiv : Mat n ≃⋆ₐ[ℂ] (Carrier hb n →ₗ[ℂ] Carrier hb n) :=
  (LinearMap.toMatrixOrthonormal (sourceBasis hb n)).symm

theorem finrank_carrier : Module.finrank ℂ (Carrier hb n) = n + 1 := by
  simpa only [Index, Fintype.card_fin] using
    Module.finrank_eq_card_basis (sourceBasis hb n).toBasis

theorem finrank_endomorphisms :
    Module.finrank ℂ (Carrier hb n →ₗ[ℂ] Carrier hb n) = (n + 1) ^ 2 := by
  rw [← (matrixEquiv hb n).toAlgEquiv.toLinearEquiv.finrank_eq]
  simp only [Mat, Index, Module.finrank_matrix, Module.finrank_self,
    Fintype.card_fin, mul_one, pow_two]

/-- The finite ladder and Weyl coordinates select the same Hermite corner. -/
theorem preparation_corner_eq :
    SourceWeylPreparation.corner hb n = SourceFiniteLadder.corner hb n := rfl

theorem preparation_projection_eq :
    SourceWeylPreparation.projection hb n = SourceFiniteLadder.projection hb n := rfl

theorem preparation_on_source_corner (M : Mat n) :
    SourceWeylPreparation.sourceAverage hb n (SourceFiniteLadder.corner hb n M) =
      (Matrix.trace M / ((n + 1 : ℕ) : ℂ)) • SourceFiniteLadder.projection hb n :=
  SourceWeylPreparation.sourceAverage_eq_trace hb n M

theorem matrixEquiv_apply_basis (M : Mat n) (j : Index n) :
    (matrixEquiv hb n M (sourceBasis hb n j) : ComplexL2) =
      FiniteHermiteCorner.corner hb (fun i : Index n => i.val) M
        (sourceBasis hb n j : ComplexL2) := by
  change (Matrix.toLin (sourceBasis hb n).toBasis (sourceBasis hb n).toBasis M
    ((sourceBasis hb n).toBasis j) : ComplexL2) = _
  rw [Matrix.toLin_self]
  simp only [Submodule.coe_sum, Submodule.coe_smul, OrthonormalBasis.coe_toBasis,
    sourceBasis_coe, FiniteHermiteCorner.corner_state hb _ Fin.val_injective]

theorem matrixEquiv_apply (M : Mat n) (v : Carrier hb n) :
    (matrixEquiv hb n M v : ComplexL2) =
      FiniteHermiteCorner.corner hb (fun i : Index n => i.val) M (v : ComplexL2) := by
  have h : (FiniteHermiteCorner.sourceSpace hb (fun i : Index n => i.val)).subtype.comp
        (matrixEquiv hb n M) =
      (FiniteHermiteCorner.corner hb (fun i : Index n => i.val) M).toLinearMap.comp
        (FiniteHermiteCorner.sourceSpace hb (fun i : Index n => i.val)).subtype := by
    apply (sourceBasis hb n).toBasis.ext
    intro j
    exact matrixEquiv_apply_basis hb n M j
  exact congrArg (fun f : Carrier hb n →ₗ[ℂ] ComplexL2 => f v) h

def sourceAnnihilator : Carrier hb n →ₗ[ℂ] Carrier hb n :=
  matrixEquiv hb n (lowering n)

def sourceCreator : Carrier hb n →ₗ[ℂ] Carrier hb n :=
  matrixEquiv hb n (lowering n).conjTranspose

@[simp] theorem sourceCreator_eq_star : sourceCreator hb n = star (sourceAnnihilator hb n) := by
  exact map_star (matrixEquiv hb n) (lowering n)

theorem sourceAnnihilator_coe (v : Carrier hb n) :
    (sourceAnnihilator hb n v : ComplexL2) =
      SourceFiniteLadder.compressedAnnihilation hb n (v : ComplexL2) :=
  matrixEquiv_apply hb n (lowering n) v

theorem sourceCreator_coe (v : Carrier hb n) :
    (sourceCreator hb n v : ComplexL2) =
      SourceFiniteLadder.compressedCreation hb n (v : ComplexL2) :=
  matrixEquiv_apply hb n (lowering n).conjTranspose v

theorem sourceAnnihilator_differential (v : Carrier hb n) :
    (sourceAnnihilator hb n v : ComplexL2) =
      embedding (annihilation b (SourceFiniteLadder.projectedCore hb n (v : ComplexL2))) := by
  rw [sourceAnnihilator_coe]
  exact (SourceFiniteLadder.embedding_annihilation_projectedCore hb n (v : ComplexL2)).symm

theorem sourceCreator_differential (v : Carrier hb n) :
    (sourceCreator hb n v : ComplexL2) =
      SourceFiniteLadder.projection hb n
        (embedding (creation b (SourceFiniteLadder.projectedCore hb n (v : ComplexL2)))) := by
  rw [sourceCreator_coe]
  exact (SourceFiniteLadder.projection_embedding_creation_projectedCore hb n
    (v : ComplexL2)).symm

/-- The finite differential annihilator and its adjoint generate every endomorphism. -/
theorem adjoin_sourceAnnihilator_eq_top :
    StarAlgebra.adjoin ℂ ({sourceAnnihilator hb n} :
      Set (Carrier hb n →ₗ[ℂ] Carrier hb n)) = ⊤ := by
  have h := StarAlgHom.map_adjoin (R := ℂ) (A := Mat n)
    (B := Carrier hb n →ₗ[ℂ] Carrier hb n) (by exact (matrixEquiv hb n).toStarAlgHom)
    ({lowering n} : Set (Mat n))
  rw [FiniteLadderAlgebra.adjoin_lowering_eq_top, Set.image_singleton] at h
  change StarAlgebra.adjoin ℂ ({(matrixEquiv hb n).toStarAlgHom (lowering n)} :
    Set (Carrier hb n →ₗ[ℂ] Carrier hb n)) = ⊤
  rw [← h]
  apply top_unique
  intro T _
  exact ⟨(matrixEquiv hb n).symm T, by trivial, (matrixEquiv hb n).apply_symm_apply T⟩

theorem matrix_coordinates_unique (T : Carrier hb n →ₗ[ℂ] Carrier hb n) :
    ∃! M : Mat n, matrixEquiv hb n M = T :=
  ⟨(matrixEquiv hb n).symm T, (matrixEquiv hb n).apply_symm_apply T,
    fun _ hM => (matrixEquiv hb n).injective (hM.trans
      ((matrixEquiv hb n).apply_symm_apply T).symm)⟩

end GeneratedFoundations.Operations.SourceFiniteCornerAlgebra
