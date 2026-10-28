module

public import GeneratedFoundations.Geometry.SourceQuotientCasimir
public import GeneratedFoundations.Geometry.SourceOneFormContinuousCore
public import GeneratedFoundations.Geometry.SourceCoefficientDifferentiation

/-!
# Finite coefficient resolution on the original quotient Haar source

Every even coefficient is retained. Products are evaluated on continuous
representatives before passing to Haar space. The coefficient heat map is
intertwined with the actual Haar heat operator, not a fitted multiplier.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceOneFormContinuousCore
open GeneratedFoundations.Geometry.SourceCoefficientDifferentiation

namespace GeneratedFoundations.Geometry.SourceScalarResolution

abbrev ScalarCore := EvenIndex →₀ ℂ

def scalarBasis : Module.Basis EvenIndex ℂ ScalarCore := Finsupp.basisSingleOne

def includeScalar : ScalarCore →ₗ[ℂ] QuotientL2 :=
  scalarBasis.constr ℂ quotientBasisVector

def representative : ScalarCore →ₗ[ℂ] C(CentralQuotient, ℂ) :=
  scalarBasis.constr ℂ (fun a =>
    normalization a.val.1 • quotientEntry a.property a.val.2.1 a.val.2.2)

@[simp] theorem includeScalar_basis (a : EvenIndex) :
    includeScalar (scalarBasis a) = quotientBasisVector a :=
  scalarBasis.constr_basis ℂ _ a

@[simp] theorem representative_basis (a : EvenIndex) :
    representative (scalarBasis a) =
      normalization a.val.1 • quotientEntry a.property a.val.2.1 a.val.2.2 :=
  scalarBasis.constr_basis ℂ _ a

theorem representative_toHaar (f : ScalarCore) :
    ContinuousMap.toLp 2 quotientHaar ℂ (representative f) = includeScalar f := by
  have h : (ContinuousMap.toLp 2 quotientHaar ℂ).toLinearMap.comp representative =
      includeScalar := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, representative_basis, map_smul, includeScalar_basis]
    rfl
  exact LinearMap.congr_fun h f

def coreHeat (t : ℝ≥0) : ScalarCore →ₗ[ℂ] ScalarCore :=
  scalarBasis.constr ℂ (fun a =>
    (Geometry.SourceHeatSemigroup.decay t a.val.1 : ℂ) • scalarBasis a)

@[simp] theorem coreHeat_basis (t : ℝ≥0) (a : EvenIndex) :
    coreHeat t (scalarBasis a) =
      (Geometry.SourceHeatSemigroup.decay t a.val.1 : ℂ) • scalarBasis a :=
  scalarBasis.constr_basis ℂ _ a

@[simp] theorem coreHeat_zero (f : ScalarCore) : coreHeat 0 f = f := by
  have h : coreHeat 0 = LinearMap.id := by
    apply scalarBasis.ext
    intro a
    simp only [coreHeat_basis, NNReal.coe_zero,
      Geometry.SourceHeatSemigroup.decay_zero, Complex.ofReal_one, one_smul,
      LinearMap.id_apply]
  exact LinearMap.congr_fun h f

theorem coreHeat_add (s t : ℝ≥0) (f : ScalarCore) :
    coreHeat (s + t) f = coreHeat s (coreHeat t f) := by
  have h : coreHeat (s + t) = (coreHeat s).comp (coreHeat t) := by
    apply scalarBasis.ext
    intro a
    simp only [coreHeat_basis, LinearMap.comp_apply, map_smul,
      NNReal.coe_add, Geometry.SourceHeatSemigroup.decay_add,
      Complex.ofReal_mul, smul_smul]
    rw [mul_comm]
  exact LinearMap.congr_fun h f

/-- This is the heat evolution in the original Haar field, with the
finite coefficient presentation retained for nonlinear evaluation. -/
theorem includeScalar_coreHeat (t : ℝ≥0) (f : ScalarCore) :
    includeScalar (coreHeat t f) = Geometry.SourceQuotientCasimir.heat t (includeScalar f) := by
  have h : includeScalar.comp (coreHeat t) =
      (Geometry.SourceQuotientCasimir.heat t).toLinearMap.comp includeScalar := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, coreHeat_basis, map_smul,
      includeScalar_basis, ContinuousLinearMap.coe_coe,
      Geometry.SourceQuotientCasimir.heat_basis]
  exact LinearMap.congr_fun h f

/-- The round source derivative on each actual coefficient row.  The
axis operators have already been identified with derivatives of source
orbits; the factor two gives the round frame normalization. -/
def derivative (L : ℝ) (j : Fin 3) :
    ScalarCore →ₗ[ℂ] C(CentralQuotient, ℂ) :=
  scalarBasis.constr ℂ (fun a =>
    ((2 / L : ℝ) : ℂ) •
      rowRepresentative a.property a.val.2.1
        (hilbertAxis a.val.1 j (sourceBasis a.val.1 a.val.2.2)))


end GeneratedFoundations.Geometry.SourceScalarResolution
