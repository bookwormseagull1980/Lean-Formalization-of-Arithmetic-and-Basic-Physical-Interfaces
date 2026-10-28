module

public import GeneratedFoundations.Geometry.SourceScalarResolution
public import GeneratedFoundations.Geometry.SourceOneFormContinuousCore

/-!
# Scalar coefficient coordinates of the differentiated one-form core

Every component of an original finite one-form has finite coordinates in
the same even scalar basis. The coordinate map is built from the original
row bases. Its continuous representative is proved equal to the original
one-form representative, before any product or Haar inclusion is taken.
-/

@[expose] public section
noncomputable section

open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Geometry.SourceOneFormContinuousCore
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormScalarCoordinates

def rowCoordinates {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗ[ℂ] SourceScalarResolution.ScalarCore :=
  (sourceBasis m).toBasis.constr ℂ (fun j =>
    SourceScalarResolution.scalarBasis ⟨⟨m, i, j⟩, hm⟩)

@[simp] theorem rowCoordinates_basis {m : ℕ} (hm : Even m)
    (i j : Fin (m + 1)) :
    rowCoordinates hm i (sourceBasis m j) =
      SourceScalarResolution.scalarBasis ⟨⟨m, i, j⟩, hm⟩ :=
  (sourceBasis m).toBasis.constr_basis ℂ _ j

theorem rowCoordinates_representative {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (v : HilbertCarrier m) :
    SourceScalarResolution.representative (rowCoordinates hm i v) =
      rowRepresentative hm i v := by
  have h : SourceScalarResolution.representative.comp (rowCoordinates hm i) =
      rowRepresentative hm i := by
    apply (sourceBasis m).toBasis.ext
    intro j
    change SourceScalarResolution.representative
        (rowCoordinates hm i (sourceBasis m j)) =
      rowRepresentative hm i (sourceBasis m j)
    rw [rowCoordinates_basis, SourceScalarResolution.representative_basis,
      rowRepresentative_basis]
  exact LinearMap.congr_fun h v

def component (j : Fin 3) : Core →ₗ[ℂ] SourceScalarResolution.ScalarCore :=
  coreBasis.constr ℂ (fun a =>
    rowCoordinates a.val.1.1.property a.val.1.2
      (curlBasis a.val.1.1.val a.val.2 j))

/-- The finite coefficient coordinates preserve the continuous function
itself; this is stronger than equality only after Haar inclusion. -/
theorem component_representative (A : Core) (j : Fin 3) :
    SourceScalarResolution.representative (component j A) = representative A j := by
  let evaluation : ContinuousField →ₗ[ℂ] C(SourceSpinCentre.CentralQuotient, ℂ) :=
    LinearMap.proj j
  have h : SourceScalarResolution.representative.comp (component j) =
      evaluation.comp representative := by
    apply coreBasis.ext
    intro a
    change SourceScalarResolution.representative (component j (coreBasis a)) =
      representative (coreBasis a) j
    rw [component, Module.Basis.constr_basis, rowCoordinates_representative,
      representative_basis]
    rfl
  exact LinearMap.congr_fun h A

end GeneratedFoundations.Geometry.SourceOneFormScalarCoordinates
