module

public import GeneratedFoundations.Geometry.SourceSymmetricPowers
public import GeneratedFoundations.Geometry.SourceCentralObservations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Unitary realization of every homogeneous source representation

Polynomial substitution has coefficients that are continuous functions of
the source matrix. The complete coefficient vector gives a finite-dimensional
coordinate space. Its Haar orbit embeds the original homogeneous submodule
into an actual `L²` space. The image inherits a positive-definite inner product,
and source action becomes measure-preserving translation of the orbit.

Continuity in the source parameter is proved in addition to continuity of
each linear operator. Neither unitarity nor irreducibility is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module MvPolynomial
open scoped BigOperators ENNReal
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers

namespace GeneratedFoundations.Geometry.SourceSymmetricUnitary

def sourceEntry (i j : Fin 2) : C(SU2, ℂ) :=
  ⟨fun U => (U : Mat2) i j,
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)⟩

def continuousVariableImage (i : Fin 2) : MvPolynomial (Fin 2) C(SU2, ℂ) :=
  ∑ j, C (sourceEntry j i) * X j

/-- Substitution over the ring of continuous source observations. -/
def continuousCoefficientAction : PolynomialSpace →+* MvPolynomial (Fin 2) C(SU2, ℂ) :=
  MvPolynomial.eval₂Hom (C.comp (algebraMap ℂ C(SU2, ℂ))) continuousVariableImage

theorem continuousCoefficientAction_at (U : SU2) (p : PolynomialSpace) :
    MvPolynomial.map (ContinuousMap.evalAlgHom ℂ ℂ U).toRingHom
        (continuousCoefficientAction p) = polynomialAction (U : Mat2) p := by
  have h : (MvPolynomial.map (ContinuousMap.evalAlgHom ℂ ℂ U).toRingHom).comp
      continuousCoefficientAction = (polynomialAction (U : Mat2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [continuousCoefficientAction, polynomialAction, MvPolynomial.algebraMap_eq]
    · intro i
      simp [continuousCoefficientAction, continuousVariableImage, variableImage, sourceEntry]
  exact RingHom.congr_fun h p

theorem polynomialAction_coefficient_continuous (p : PolynomialSpace) (d : Fin 2 →₀ ℕ) :
    Continuous (fun U : SU2 => (polynomialAction (U : Mat2) p).coeff d) := by
  have heq : (fun U : SU2 => (polynomialAction (U : Mat2) p).coeff d) =
      fun U => (continuousCoefficientAction p).coeff d U := by
    funext U
    rw [← continuousCoefficientAction_at U p, MvPolynomial.coeff_map]
    rfl
  rw [heq]
  exact ContinuousMap.continuous _

abbrev Coordinate (m : ℕ) := EuclideanSpace ℂ (Fin (m + 1))

/-- All homogeneous coefficients, with their actual exponents. -/
def coefficientVector (m : ℕ) : Carrier m →ₗ[ℂ] Coordinate m where
  toFun p := WithLp.toLp 2 (fun k => (p : PolynomialSpace).coeff (exponentOfIndex m k).val)
  map_add' p q := by
    ext k
    exact congrArg (fun f : (Fin 2 →₀ ℕ) →₀ ℂ => f (exponentOfIndex m k).val)
      (AddMonoidAlgebra.coeff_add (p : PolynomialSpace) (q : PolynomialSpace))
  map_smul' c p := by
    ext k
    exact MvPolynomial.coeff_smul _ _ _

@[simp] theorem coefficientVector_apply (m : ℕ) (p : Carrier m) (k : Fin (m + 1)) :
    coefficientVector m p k = (p : PolynomialSpace).coeff (exponentOfIndex m k).val := rfl

theorem coefficientVector_injective (m : ℕ) : Function.Injective (coefficientVector m) := by
  intro p q hpq
  apply Subtype.ext
  ext d
  by_cases hd : d.degree = m
  · let k := exponentEquiv m ⟨d, hd⟩
    have hk : (exponentOfIndex m k).val = d :=
      congrArg Subtype.val ((exponentEquiv m).symm_apply_apply ⟨d, hd⟩)
    have hc := congrArg (fun v : Coordinate m => v k) hpq
    simpa only [coefficientVector_apply, hk] using hc
  · rw [p.property.coeff_eq_zero hd, q.property.coeff_eq_zero hd]

/-- This equivalence improves the complete coefficient map; it is not an
abstract identification of vector spaces of the same dimension. -/
def coefficientEquiv (m : ℕ) : Carrier m ≃ₗ[ℂ] Coordinate m :=
  LinearEquiv.ofInjectiveOfFinrankEq (coefficientVector m) (coefficientVector_injective m)
    (by rw [carrier_finrank, finrank_euclideanSpace_fin])

@[simp] theorem coefficientEquiv_apply (m : ℕ) (p : Carrier m) :
    coefficientEquiv m p = coefficientVector m p := rfl

theorem coefficientOrbit_continuous (m : ℕ) (p : Carrier m) :
    Continuous (fun U : SU2 => coefficientVector m (sourceRepresentation m U p)) := by
  change Continuous (fun U : SU2 => WithLp.toLp 2
    (fun k => (polynomialAction (U : Mat2) (p : PolynomialSpace)).coeff
      (exponentOfIndex m k).val))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun k =>
    polynomialAction_coefficient_continuous _ _))

instance sourceMeasurableSpace : MeasurableSpace SU2 := borel SU2

instance sourceBorelSpace : BorelSpace SU2 := ⟨rfl⟩

def sourceHaar : Measure SU2 :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)

instance sourceHaar_isHaar : Measure.IsHaarMeasure sourceHaar :=
  inferInstanceAs (Measure.IsHaarMeasure
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)))

instance sourceHaar_isProbability : IsProbabilityMeasure sourceHaar where
  measure_univ := Measure.haarMeasure_self

/-- Inversion makes the original left action correspond to left translation
of the orbit argument with respect to the same normalized Haar measure. -/
def orbitContinuous (m : ℕ) (p : Carrier m) : C(SU2, Coordinate m) :=
  ⟨fun U => coefficientVector m (sourceRepresentation m U⁻¹ p),
    (coefficientOrbit_continuous m p).comp continuous_inv⟩

@[simp] theorem orbitContinuous_apply (m : ℕ) (p : Carrier m) (U : SU2) :
    orbitContinuous m p U = coefficientVector m (sourceRepresentation m U⁻¹ p) := rfl

@[simp] theorem orbitContinuous_one (m : ℕ) (p : Carrier m) :
    orbitContinuous m p 1 = coefficientVector m p := by
  simp only [orbitContinuous_apply, inv_one, map_one, Module.End.one_apply]

def orbitContinuousLinear (m : ℕ) : Carrier m →ₗ[ℂ] C(SU2, Coordinate m) where
  toFun := orbitContinuous m
  map_add' p q := by ext U; simp only [orbitContinuous_apply, map_add, ContinuousMap.add_apply]
  map_smul' c p := by
    apply ContinuousMap.ext
    intro U
    change coefficientVector m (sourceRepresentation m U⁻¹ (c • p)) =
      c • coefficientVector m (sourceRepresentation m U⁻¹ p)
    rw [map_smul, map_smul]

abbrev OrbitL2 (m : ℕ) := Lp (Coordinate m) 2 sourceHaar

def orbitEmbedding (m : ℕ) : Carrier m →ₗ[ℂ] OrbitL2 m :=
  (ContinuousMap.toLp 2 sourceHaar ℂ).toLinearMap.comp (orbitContinuousLinear m)

theorem orbitEmbedding_injective (m : ℕ) : Function.Injective (orbitEmbedding m) := by
  intro p q hpq
  apply coefficientVector_injective m
  have hc : orbitContinuous m p = orbitContinuous m q :=
    (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) sourceHaar) hpq
  have h1 := congrArg (fun f : C(SU2, Coordinate m) => f 1) hc
  simpa only [orbitContinuous_one] using h1

/-- The finite-dimensional subspace of actual Haar `L²` source orbits. -/
abbrev HilbertCarrier (m : ℕ) := LinearMap.range (orbitEmbedding m)

instance hilbertCarrier_finiteDimensional (m : ℕ) :
    FiniteDimensional ℂ (HilbertCarrier m) := inferInstance

def carrierEquiv (m : ℕ) : Carrier m ≃ₗ[ℂ] HilbertCarrier m :=
  LinearEquiv.ofInjective (orbitEmbedding m) (orbitEmbedding_injective m)

@[simp] theorem carrierEquiv_coe (m : ℕ) (p : Carrier m) :
    (carrierEquiv m p : OrbitL2 m) = orbitEmbedding m p := rfl

theorem hilbertCarrier_finrank (m : ℕ) : Module.finrank ℂ (HilbertCarrier m) = m + 1 := by
  rw [← (carrierEquiv m).finrank_eq, carrier_finrank]

def sourceLinearEquiv (m : ℕ) (U : SU2) : Carrier m ≃ₗ[ℂ] Carrier m where
  toLinearMap := sourceRepresentation m U
  invFun := sourceRepresentation m U⁻¹
  left_inv := (sourceRepresentation m).inv_self_apply U
  right_inv := (sourceRepresentation m).self_inv_apply U

def realizedLinearEquiv (m : ℕ) (U : SU2) : HilbertCarrier m ≃ₗ[ℂ] HilbertCarrier m :=
  ((carrierEquiv m).symm.trans (sourceLinearEquiv m U)).trans (carrierEquiv m)

@[simp] theorem realizedLinearEquiv_apply_carrier (m : ℕ) (U : SU2) (p : Carrier m) :
    realizedLinearEquiv m U (carrierEquiv m p) =
      carrierEquiv m (sourceRepresentation m U p) := by
  change carrierEquiv m (sourceRepresentation m U ((carrierEquiv m).symm
    (carrierEquiv m p))) = _
  rw [LinearEquiv.symm_apply_apply]

def orbitTranslation (m : ℕ) (U : SU2) : OrbitL2 m →ₗᵢ[ℂ] OrbitL2 m :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun V : SU2 => U⁻¹ * V)
    (measurePreserving_mul_left sourceHaar U⁻¹)

theorem orbitEmbedding_intertwines (m : ℕ) (U : SU2) (p : Carrier m) :
    orbitEmbedding m (sourceRepresentation m U p) = orbitTranslation m U (orbitEmbedding m p) := by
  apply Lp.ext
  have hleft : orbitEmbedding m (sourceRepresentation m U p) =ᵐ[sourceHaar]
      orbitContinuous m (sourceRepresentation m U p) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
      (orbitContinuous m (sourceRepresentation m U p))
  have hright : orbitTranslation m U (orbitEmbedding m p) =ᵐ[sourceHaar]
      fun V => orbitEmbedding m p (U⁻¹ * V) :=
    Lp.coeFn_compMeasurePreserving (orbitEmbedding m p)
      (measurePreserving_mul_left sourceHaar U⁻¹)
  have horbit := (measurePreserving_mul_left sourceHaar U⁻¹).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar (orbitContinuous m p))
  filter_upwards [hleft, hright, horbit] with V hl hr ho
  change orbitEmbedding m p (U⁻¹ * V) = orbitContinuous m p (U⁻¹ * V) at ho
  rw [hr, ho, hl]
  simp only [orbitContinuous_apply, mul_inv_rev, inv_inv]
  rw [map_mul, Module.End.mul_apply]

theorem realizedLinearEquiv_coe (m : ℕ) (U : SU2) (p : HilbertCarrier m) :
    (realizedLinearEquiv m U p : OrbitL2 m) = orbitTranslation m U (p : OrbitL2 m) := by
  obtain ⟨q, rfl⟩ := (carrierEquiv m).surjective p
  rw [realizedLinearEquiv_apply_carrier, carrierEquiv_coe, carrierEquiv_coe,
    orbitEmbedding_intertwines]

/-- Unitarity is inherited from measure-preserving translation, after
injectivity of the original polynomial orbit has been proved. -/
def unitaryAction (m : ℕ) (U : SU2) : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m where
  toLinearEquiv := realizedLinearEquiv m U
  norm_map' p := by
    change ‖(realizedLinearEquiv m U p : OrbitL2 m)‖ = ‖(p : OrbitL2 m)‖
    rw [realizedLinearEquiv_coe, (orbitTranslation m U).norm_map]

@[simp] theorem unitaryAction_apply_carrier (m : ℕ) (U : SU2) (p : Carrier m) :
    unitaryAction m U (carrierEquiv m p) = carrierEquiv m (sourceRepresentation m U p) :=
  realizedLinearEquiv_apply_carrier m U p

def unitaryRepresentation (m : ℕ) : SU2 →* (HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m) where
  toFun := unitaryAction m
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro p
    obtain ⟨q, rfl⟩ := (carrierEquiv m).surjective p
    simp only [unitaryAction_apply_carrier, map_one, Module.End.one_apply,
      LinearIsometryEquiv.coe_one, id_eq]
  map_mul' U V := by
    apply LinearIsometryEquiv.ext
    intro p
    obtain ⟨q, rfl⟩ := (carrierEquiv m).surjective p
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, unitaryAction_apply_carrier,
      map_mul, Module.End.mul_apply]

/-- The invariant positive-definite pairing on the original polynomial carrier. -/
def sourceInner (m : ℕ) (p q : Carrier m) : ℂ :=
  inner ℂ (carrierEquiv m p) (carrierEquiv m q)

theorem sourceInner_definite (m : ℕ) (p : Carrier m) : sourceInner m p p = 0 ↔ p = 0 := by
  rw [sourceInner, inner_self_eq_zero]
  exact (carrierEquiv m).map_eq_zero_iff

@[instance_reducible]
def sourceInnerCore (m : ℕ) : InnerProductSpace.Core ℂ (Carrier m) where
  inner := sourceInner m
  conj_inner_symm p q := inner_conj_symm (carrierEquiv m p) (carrierEquiv m q)
  re_inner_nonneg p := inner_self_nonneg
  add_left p q r := by simp only [sourceInner, map_add, inner_add_left]
  smul_left p q c := by
    simp only [sourceInner, map_smul]
    exact inner_smul_left (carrierEquiv m p) (carrierEquiv m q) c
  definite p hp := (sourceInner_definite m p).mp hp

theorem sourceInner_invariant (m : ℕ) (U : SU2) (p q : Carrier m) :
    sourceInner m (sourceRepresentation m U p) (sourceRepresentation m U q) =
      sourceInner m p q := by
  change inner ℂ (carrierEquiv m (sourceRepresentation m U p))
    (carrierEquiv m (sourceRepresentation m U q)) = _
  rw [← unitaryAction_apply_carrier, ← unitaryAction_apply_carrier]
  exact (unitaryAction m U).inner_map_map _ _

def hilbertCoordinate (m : ℕ) : HilbertCarrier m ≃L[ℂ] Coordinate m :=
  ((carrierEquiv m).symm.trans (coefficientEquiv m)).toContinuousLinearEquiv

theorem unitaryAction_orbit_continuous (m : ℕ) (p : HilbertCarrier m) :
    Continuous (fun U : SU2 => unitaryAction m U p) := by
  obtain ⟨q, rfl⟩ := (carrierEquiv m).surjective p
  have heq : (fun U : SU2 => unitaryAction m U (carrierEquiv m q)) =
      fun U => (hilbertCoordinate m).symm
        (coefficientVector m (sourceRepresentation m U q)) := by
    funext U
    apply (hilbertCoordinate m).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, unitaryAction_apply_carrier]
    change coefficientEquiv m ((carrierEquiv m).symm
      (carrierEquiv m (sourceRepresentation m U q))) = _
    rw [LinearEquiv.symm_apply_apply, coefficientEquiv_apply]
  rw [heq]
  exact (hilbertCoordinate m).symm.continuous.comp (coefficientOrbit_continuous m q)

/-- The group and vector variables vary jointly in the actual Hilbert realization. -/
theorem unitaryAction_joint_continuous (m : ℕ) :
    Continuous (fun p : SU2 × HilbertCarrier m => unitaryAction m p.1 p.2) := by
  let B := (monomialBasis m).map (carrierEquiv m)
  have heq : (fun p : SU2 × HilbertCarrier m => unitaryAction m p.1 p.2) =
      fun p => ∑ i : Fin (m + 1), B.equivFun p.2 i • unitaryAction m p.1 (B i) := by
    funext p
    conv_lhs => rw [← B.sum_equivFun p.2]
    rw [map_sum]
    simp only [map_smul]
  rw [heq]
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp B.equivFunL.continuous).comp continuous_snd).smul
    ((unitaryAction_orbit_continuous m (B i)).comp continuous_fst)

end GeneratedFoundations.Geometry.SourceSymmetricUnitary
