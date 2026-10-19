module

public import GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy

/-!
# Continuous representatives of the differentiated field core

The representatives are finite sums of the original even source matrix
coefficients. Passing to the quotient Haar class gives exactly the existing
field, so products used in the nonlinear curvature are formed on the same
compact carrier. No representative of an arbitrary L2 equivalence class is
selected, and no regularity premise is imposed on a caller.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormContinuousCore

abbrev ContinuousField := Fin 3 → C(CentralQuotient, ℂ)

def toHaar : ContinuousField →ₗ[ℂ] OneFormL2 where
  toFun f := WithLp.toLp 2 (fun j => ContinuousMap.toLp 2 quotientHaar ℂ (f j))
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
    funext j
    exact map_add (ContinuousMap.toLp 2 quotientHaar ℂ) (f j) (g j)
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
    funext j
    exact map_smul (ContinuousMap.toLp 2 quotientHaar ℂ) c (f j)

def rowRepresentative {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗ[ℂ] C(CentralQuotient, ℂ) :=
  (sourceBasis m).toBasis.constr ℂ
    (fun j => normalization m • quotientEntry hm i j)

@[simp] theorem rowRepresentative_basis {m : ℕ} (hm : Even m)
    (i j : Fin (m + 1)) :
    rowRepresentative hm i (sourceBasis m j) = normalization m • quotientEntry hm i j :=
  (sourceBasis m).toBasis.constr_basis ℂ _ j

theorem rowRepresentative_toLp {m : ℕ} (hm : Even m) (i : Fin (m + 1))
    (v : HilbertCarrier m) :
    ContinuousMap.toLp 2 quotientHaar ℂ (rowRepresentative hm i v) =
      rowIsometry hm i v := by
  have h : (ContinuousMap.toLp 2 quotientHaar ℂ).toLinearMap.comp
      (rowRepresentative hm i) = rowLinear hm i := by
    apply (sourceBasis m).toBasis.ext
    intro j
    change ContinuousMap.toLp 2 quotientHaar ℂ
      (rowRepresentative hm i (sourceBasis m j)) = rowLinear hm i (sourceBasis m j)
    rw [rowRepresentative_basis, map_smul, rowLinear_basis]
    rfl
  exact LinearMap.congr_fun h v

def eigenRepresentative (a : CurlIndex) : ContinuousField :=
  fun j => rowRepresentative a.1.1.property a.1.2 (curlBasis a.1.1.val a.2 j)

theorem eigenRepresentative_toHaar (a : CurlIndex) :
    toHaar (eigenRepresentative a) = eigenfield a := by
  apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
  funext j
  change ContinuousMap.toLp 2 quotientHaar ℂ
    (rowRepresentative a.1.1.property a.1.2 (curlBasis a.1.1.val a.2 j)) =
      rowIsometry a.1.1.property a.1.2 (curlBasis a.1.1.val a.2 j)
  exact rowRepresentative_toLp _ _ _

def representative : Core →ₗ[ℂ] ContinuousField :=
  coreBasis.constr ℂ (fun a => eigenRepresentative a.val)

@[simp] theorem representative_basis (a : CoclosedIndex) :
    representative (coreBasis a) = eigenRepresentative a.val :=
  coreBasis.constr_basis ℂ _ a

/-- The nonlinear representative belongs to the very same original Haar
field. This identity also applies to its actual differentiated curl. -/
theorem representative_toHaar (A : Core) :
    toHaar (representative A) = includeCore A := by
  have h : toHaar.comp representative = includeCore := by
    apply coreBasis.ext
    intro a
    change toHaar (representative (coreBasis a)) = includeCore (coreBasis a)
    rw [representative_basis, eigenRepresentative_toHaar, includeCore_basis]
  exact LinearMap.congr_fun h A

theorem differentiated_representative_toHaar (A : Core) :
    toHaar (representative (coreCurl A)) = closedCurl (coreToCurlDomain A) := by
  rw [representative_toHaar, coreCurl_is_differential]

end GeneratedFoundations.Geometry.SourceOneFormContinuousCore
