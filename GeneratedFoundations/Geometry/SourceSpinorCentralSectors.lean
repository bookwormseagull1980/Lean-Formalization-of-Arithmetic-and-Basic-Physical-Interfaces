module

public import GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
public import GeneratedFoundations.Geometry.SourceCentralSpectralProjection

/-!
# The actual central pullback preserves the closed source spinor

The central operation is pullback by the original group centre on each
Haar component. Its degree character follows from the source polynomial
action. It preserves the full closed differential domain and commutes with
the closed Dirac operator. Thus parity is a property of actual fields,
rather than a selection made from a supplied spectral table.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorHilbertSum
open GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceSpinorCentralSectors

def centralLinear : SpinorL2 →ₗ[ℂ] SpinorL2 where
  toFun F := WithLp.toLp 2 fun i => centralPullback (F i)
  map_add' F G := by
    apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
    exact funext fun i => map_add centralPullback (F i) (G i)
  map_smul' c F := by
    apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
    exact funext fun i => map_smul centralPullback c (F i)

theorem centralLinear_inner_map (F G : SpinorL2) :
    inner ℂ (centralLinear F) (centralLinear G) = inner ℂ F G := by
  simp only [PiLp.inner_apply, centralLinear, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometry.inner_map_map]

def central : SpinorL2 →ₗᵢ[ℂ] SpinorL2 :=
  centralLinear.isometryOfInner centralLinear_inner_map

theorem central_twice (F : SpinorL2) : central (central F) = F := by
  apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
  exact funext fun i => centralPullback_twice (F i)

theorem central_inner (F G : SpinorL2) :
    inner ℂ (central F) G = inner ℂ F (central G) := by
  have h := central.inner_map_map F (central G)
  simpa only [central_twice] using h

theorem central_scalarRow (m : ℕ) (i : Fin (m + 1)) (a : HilbertCarrier m) :
    centralPullback (scalarRowIsometry m i a) =
      (-1 : ℂ) ^ m • scalarRowIsometry m i a := by
  have hmaps : centralPullback.toLinearMap.comp (scalarRowIsometry m i).toLinearMap =
      (-1 : ℂ) ^ m • (scalarRowIsometry m i).toLinearMap := by
    apply (sourceBasis m).toBasis.ext
    intro j
    change centralPullback (scalarRowIsometry m i (sourceBasis m j)) =
      (-1 : ℂ) ^ m • scalarRowIsometry m i (sourceBasis m j)
    rw [scalarRowIsometry_basis, centralPullback_basis]
  exact LinearMap.congr_fun hmaps a

theorem central_row (r : RowIndex) (A : SpinorBlock r.1) :
    central (blockEmbedding r A) = (-1 : ℂ) ^ r.1 • blockEmbedding r A := by
  apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
  exact funext fun i => central_scalarRow r.1 r.2 (A i)

theorem central_eigenfield (a : SpinIndex) :
    central (eigenfield a) = (-1 : ℂ) ^ a.1.1 • eigenfield a :=
  central_row a.1 _

theorem central_coefficients (F : SpinorL2) (a : SpinIndex) :
    inner ℂ (eigenfield a) (central F) =
      (-1 : ℂ) ^ a.1.1 * inner ℂ (eigenfield a) F := by
  rw [← central_inner, central_eigenfield, inner_smul_left]
  simp only [map_pow, map_neg, map_one]

theorem central_mem_closed_domain (F : closedDirac.domain) :
    central (F : SpinorL2) ∈ closedDirac.domain := by
  have hF := (closedDirac_domain (F : SpinorL2)).mp F.property
  apply (closedDirac_domain _).mpr
  simpa only [central_coefficients, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul] using hF

/-- The same geometric centre commutes with the complete closed operator,
including every field in its full weighted-square domain. -/
theorem closedDirac_central (F : closedDirac.domain) :
    closedDirac ⟨central (F : SpinorL2), central_mem_closed_domain F⟩ =
      central (closedDirac F) := by
  apply EigenbasisClosure.eq_of_coefficients diracHilbertBasis
  intro a
  rw [diracHilbertBasis_apply, closedDirac_coefficients,
    central_coefficients, central_coefficients, closedDirac_coefficients]
  ring

def evenSector : Submodule ℂ SpinorL2 :=
  LinearMap.ker (central.toLinearMap - (1 : Module.End ℂ SpinorL2))

def oddSector : Submodule ℂ SpinorL2 :=
  LinearMap.ker (central.toLinearMap + (1 : Module.End ℂ SpinorL2))

theorem eigenfield_mem_even {a : SpinIndex} (ha : Even a.1.1) :
    eigenfield a ∈ evenSector := by
  change central (eigenfield a) - eigenfield a = 0
  rw [central_eigenfield, ha.neg_one_pow, one_smul, sub_self]

theorem eigenfield_mem_odd {a : SpinIndex} (ha : Odd a.1.1) :
    eigenfield a ∈ oddSector := by
  change central (eigenfield a) + eigenfield a = 0
  rw [central_eigenfield, ha.neg_one_pow, neg_one_smul, neg_add_cancel]

end GeneratedFoundations.Geometry.SourceSpinorCentralSectors
