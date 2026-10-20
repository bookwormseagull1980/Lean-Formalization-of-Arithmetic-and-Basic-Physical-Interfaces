module

public import GeneratedFoundations.Geometry.SourceQuotientCasimir
public import GeneratedFoundations.Physical.SourceHaarYangMillsAction
public import GeneratedFoundations.Physical.SourceChiralCarrier

/-!
# Gaussian resolution of the complete gauge and matter response

Finite fields use every even matrix coefficient of the generated source.
Their heat map is intertwined with the existing quotient Haar heat map.
Curvature and the covariant matter derivative are evaluated on continuous
representatives, including their full products, before passing to Haar space.
In particular their outputs are not projected back into the initial core.

The compensation records the difference between resolving a response and
forming the response of resolved fields.  Its cocycle is a semigroup
identity; it does not identify resolution with physical time evolution.
The sixteen matter coordinates are those of the complete source carrier.
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
open GeneratedFoundations.Physical.SourceChiralCarrier

namespace GeneratedFoundations.Physical.SourceResolutionCompensation

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

abbrev Connection := Fin 3 → Fin 8 → ScalarCore
abbrev Matter := FullIndex → ScalarCore
abbrev Fields := Connection × Matter
abbrev CurvatureFields := Fin 3 → Fin 8 → QuotientL2
abbrev MatterResponseFields := Fin 3 → FullIndex → QuotientL2
abbrev Responses := CurvatureFields × MatterResponseFields

def fieldsHeat (t : ℝ≥0) (U : Fields) : Fields :=
  (fun j a => coreHeat t (U.1 j a), fun i => coreHeat t (U.2 i))

@[simp] theorem fieldsHeat_zero (U : Fields) : fieldsHeat 0 U = U := by
  apply Prod.ext <;> funext i <;> simp [fieldsHeat]

theorem fieldsHeat_add (s t : ℝ≥0) (U : Fields) :
    fieldsHeat (s + t) U = fieldsHeat s (fieldsHeat t U) := by
  apply Prod.ext
  · funext j a
    exact coreHeat_add s t (U.1 j a)
  · funext i
    exact coreHeat_add s t (U.2 i)

def responseHeat (t : ℝ≥0) : Responses →ₗ[ℂ] Responses where
  toFun R :=
    (fun j a => Geometry.SourceQuotientCasimir.heat t (R.1 j a),
     fun j i => Geometry.SourceQuotientCasimir.heat t (R.2 j i))
  map_add' R S := by
    apply Prod.ext <;> funext j a <;> exact map_add _ _ _
  map_smul' c R := by
    apply Prod.ext
    · funext j a
      exact map_smul (Geometry.SourceQuotientCasimir.heat t) c (R.1 j a)
    · funext j a
      exact map_smul (Geometry.SourceQuotientCasimir.heat t) c (R.2 j a)

@[simp] theorem responseHeat_zero (R : Responses) : responseHeat 0 R = R := by
  apply Prod.ext <;> funext j a <;> exact Geometry.SourceQuotientCasimir.heat_zero _

theorem responseHeat_add (s t : ℝ≥0) (R : Responses) :
    responseHeat (s + t) R = responseHeat s (responseHeat t R) := by
  apply Prod.ext <;> funext j a <;> exact Geometry.SourceQuotientCasimir.heat_add s t _

theorem responseHeat_sub (t : ℝ≥0) (R S : Responses) :
    responseHeat t (R - S) = responseHeat t R - responseHeat t S := by
  apply Prod.ext
  · funext j a
    exact map_sub (Geometry.SourceQuotientCasimir.heat t) (R.1 j a) (S.1 j a)
  · funext j i
    exact map_sub (Geometry.SourceQuotientCasimir.heat t) (R.2 j i) (S.2 j i)

/-- The colour action on every complete matter coordinate.  It acts on
the generated triplet and vanishes on the colour scalar, on both chiral
copies and both spin coordinates. -/
def colourProduct (A : Fin 8 → ScalarCore) (psi : Matter) (i : FullIndex) :
    C(CentralQuotient, ℂ) :=
  match i.1 with
  | Sum.inl c => ∑ d : Fin 3, (∑ b : Fin 8,
      (Complex.I * SourceColourCasimir.generator b c d) • representative (A b)) *
        representative (psi (Sum.inl d, i.2))
  | Sum.inr _ => 0

/-- All cyclic curvature components, with the differentiated linear
terms, round frame bracket and complete nonabelian product. -/
def curvature (L : ℝ) (A : Connection) : CurvatureFields := fun j a =>
  ContinuousMap.toLp 2 quotientHaar ℂ
    (derivative L j (A (j + 1) a) - derivative L (j + 1) (A j a) -
      ((2 / L : ℝ) : ℂ) • representative (A (j + 2) a) +
      SourceHaarYangMillsAction.continuousBracket
        (fun b => representative (A j b))
        (fun b => representative (A (j + 1) b)) a)

def matterDerivative (L : ℝ) (U : Fields) : MatterResponseFields := fun j i =>
  ContinuousMap.toLp 2 quotientHaar ℂ
    (derivative L j (U.2 i) + colourProduct (U.1 j) U.2 i)

def response (L : ℝ) (U : Fields) : Responses :=
  (curvature L U.1, matterDerivative L U)

def compensation (L : ℝ) (t : ℝ≥0) (U : Fields) : Responses :=
  responseHeat t (response L U) - response L (fieldsHeat t U)

@[simp] theorem compensation_zero (L : ℝ) (U : Fields) : compensation L 0 U = 0 := by
  simp [compensation]

/-- The two defects on successive resolutions add after transporting
the first defect by the same source heat map. -/
theorem compensation_cocycle (L : ℝ) (s t : ℝ≥0) (U : Fields) :
    compensation L (s + t) U =
      responseHeat s (compensation L t U) + compensation L s (fieldsHeat t U) := by
  change responseHeat (s + t) (response L U) - response L (fieldsHeat (s + t) U) =
    responseHeat s (responseHeat t (response L U) - response L (fieldsHeat t U)) +
      (responseHeat s (response L (fieldsHeat t U)) -
        response L (fieldsHeat s (fieldsHeat t U)))
  rw [responseHeat_add, fieldsHeat_add, responseHeat_sub]
  abel

def resolution (L : ℝ) (t : ℝ≥0) (state : Fields × Responses) : Fields × Responses :=
  (fieldsHeat t state.1, responseHeat t state.2 + compensation L t state.1)

@[simp] theorem resolution_zero (L : ℝ) (state : Fields × Responses) :
    resolution L 0 state = state := by
  simp [resolution]

theorem resolution_add (L : ℝ) (s t : ℝ≥0) (state : Fields × Responses) :
    resolution L (s + t) state = resolution L s (resolution L t state) := by
  apply Prod.ext
  · exact fieldsHeat_add s t state.1
  · change responseHeat (s + t) state.2 + compensation L (s + t) state.1 = _
    rw [responseHeat_add, compensation_cocycle]
    simp only [resolution, map_add]
    abel

/-- Response plus residual is transported exactly; the response itself
need not have a constant value as the resolution changes. -/
theorem complete_response_transport (L : ℝ) (t : ℝ≥0) (state : Fields × Responses) :
    response L (resolution L t state).1 + (resolution L t state).2 =
      responseHeat t (response L state.1 + state.2) := by
  simp only [resolution, compensation, map_add]
  abel

/-- Once the field heat map and complete response are fixed, there is
exactly one compatible unresolved response. -/
theorem residual_unique (L : ℝ) (t : ℝ≥0) (U : Fields) (R S : Responses)
    (h : response L (fieldsHeat t U) + S = responseHeat t (response L U + R)) :
    S = responseHeat t R + compensation L t U := by
  calc
    S = (response L (fieldsHeat t U) + S) - response L (fieldsHeat t U) := by abel
    _ = responseHeat t (response L U + R) - response L (fieldsHeat t U) := by rw [h]
    _ = responseHeat t R + compensation L t U := by
      rw [map_add]
      dsimp [compensation]
      abel

end GeneratedFoundations.Physical.SourceResolutionCompensation
