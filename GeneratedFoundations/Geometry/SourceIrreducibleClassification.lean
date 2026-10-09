module

public import GeneratedFoundations.Geometry.SourceCompleteCoefficients
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Classification by the actual complete source coefficients

A continuous irreducible unitary representation is compared with the actual
homogeneous source carriers by a vector-valued Haar average. Completeness of
the previously constructed matrix coefficients forces a nonzero intertwiner.
Schur's lemma makes it bijective, and its Gram operator fixes a positive
normalization to a unitary intertwiner. Only the homogeneous degree is unique;
no uniqueness of an individual intertwining isometry is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSymmetricIrreducible
open GeneratedFoundations.Geometry.SourceSchurOrthogonality

namespace GeneratedFoundations.Geometry.SourceIrreducibleClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

/-- The linear representation underlying the given unitary group action. -/
def linearRepresentation (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) : Representation ℂ SU2 H where
  toFun U := (ρ U).toLinearEquiv.toLinearMap
  map_one' := by
    ext v
    exact congrArg (fun e : H ≃ₗᵢ[ℂ] H => e v) ρ.map_one
  map_mul' U V := by
    ext v
    exact congrArg (fun e : H ≃ₗᵢ[ℂ] H => e v) (ρ.map_mul U V)

variable (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H))

omit [FiniteDimensional ℂ H] in
theorem action_one (v : H) : ρ 1 v = v :=
  congrArg (fun e : H ≃ₗᵢ[ℂ] H => e v) ρ.map_one

omit [FiniteDimensional ℂ H] in
theorem target_action_mul (U V : SU2) (v : H) : ρ (U * V) v = ρ U (ρ V v) :=
  congrArg (fun e : H ≃ₗᵢ[ℂ] H => e v) (ρ.map_mul U V)

variable (hcont : ∀ v : H, Continuous (fun U : SU2 => ρ U v))

def coefficient (v b : H) : C(SU2, ℂ) :=
  ⟨fun U => inner ℂ v (ρ U b), continuous_const.inner (hcont b)⟩

omit [FiniteDimensional ℂ H] in
@[simp] theorem coefficient_apply (v b : H) (U : SU2) :
    coefficient ρ hcont v b U = inner ℂ v (ρ U b) := rfl

def orbitRankOne (m : ℕ) (a : HilbertCarrier m) (b : H)
    (v : HilbertCarrier m) (U : SU2) : H :=
  inner ℂ (unitaryAction m U a) v • ρ U b

omit [FiniteDimensional ℂ H] in
include hcont in
theorem orbitRankOne_continuous (m : ℕ) (a : HilbertCarrier m)
    (b : H) (v : HilbertCarrier m) :
    Continuous (orbitRankOne ρ m a b v) :=
  ((unitaryAction_orbit_continuous m a).inner continuous_const).smul (hcont b)

omit [FiniteDimensional ℂ H] in
include hcont in
theorem orbitRankOne_integrable (m : ℕ) (a : HilbertCarrier m)
    (b : H) (v : HilbertCarrier m) :
    Integrable (orbitRankOne ρ m a b v) sourceHaar :=
  (orbitRankOne_continuous ρ hcont m a b v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- This is an actual vector-valued average in the original source Haar measure. -/
def average (m : ℕ) (a : HilbertCarrier m) (b : H) : HilbertCarrier m →ₗ[ℂ] H where
  toFun v := ∫ U, orbitRankOne ρ m a b v U ∂sourceHaar
  map_add' v w := by
    simp only [orbitRankOne, inner_add_right, add_smul]
    exact integral_add (orbitRankOne_integrable ρ hcont m a b v)
      (orbitRankOne_integrable ρ hcont m a b w)
  map_smul' c v := by
    simp only [orbitRankOne, inner_smul_right, mul_smul, integral_smul, RingHom.id_apply]

omit [FiniteDimensional ℂ H] in
@[simp] theorem average_apply (m : ℕ) (a : HilbertCarrier m)
    (b : H) (v : HilbertCarrier m) :
    average ρ hcont m a b v = ∫ U, orbitRankOne ρ m a b v U ∂sourceHaar := rfl

omit [FiniteDimensional ℂ H] in
theorem orbitRankOne_translate (m : ℕ) (a : HilbertCarrier m)
    (b : H) (v : HilbertCarrier m) (V U : SU2) :
    orbitRankOne ρ m a b (unitaryAction m V v) (V * U) =
      ρ V (orbitRankOne ρ m a b v U) := by
  simp only [orbitRankOne, action_mul, target_action_mul,
    (unitaryAction m V).inner_map_map, map_smul]

theorem average_intertwines (m : ℕ) (a : HilbertCarrier m)
    (b : H) (V : SU2) (v : HilbertCarrier m) :
    average ρ hcont m a b (unitaryAction m V v) = ρ V (average ρ hcont m a b v) := by
  calc
    _ = ∫ U, orbitRankOne ρ m a b (unitaryAction m V v) (V * U) ∂sourceHaar :=
      (integral_mul_left_eq_self _ V).symm
    _ = ∫ U, ρ V (orbitRankOne ρ m a b v U) ∂sourceHaar := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact orbitRankOne_translate ρ m a b v V U
    _ = _ := (ρ V).toLinearIsometry.integral_comp_comm _

def averageIntertwiner (m : ℕ) (a : HilbertCarrier m) (b : H) :
    Representation.IntertwiningMap (hilbertRepresentation m) (linearRepresentation ρ) where
  toLinearMap := average ρ hcont m a b
  isIntertwining' U := by
    ext v
    exact average_intertwines ρ hcont m a b U v

theorem coefficient_integral_eq_average (m : ℕ) (v a : HilbertCarrier m) (w b : H) :
    (∫ U, conj (matrixCoefficient m v a U) * coefficient ρ hcont w b U ∂sourceHaar) =
      inner ℂ w (average ρ hcont m a b v) := by
  rw [average_apply, ← integral_inner (orbitRankOne_integrable ρ hcont m a b v) w]
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [matrixCoefficient_apply, coefficient_apply, orbitRankOne,
    inner_smul_right, inner_conj_symm]

include hcont in
/-- A nonzero continuous diagonal coefficient cannot vanish against the
complete system of actual source coefficients. -/
theorem exists_nonzero_intertwiner
    [Representation.IsIrreducible (linearRepresentation ρ)] :
    ∃ m : ℕ, ∃ T : Representation.IntertwiningMap
      (hilbertRepresentation m) (linearRepresentation ρ), T ≠ 0 := by
  let : Nontrivial (linearRepresentation ρ).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ SU2) (linearRepresentation ρ).asModule
  let : Nontrivial H := (linearRepresentation ρ).asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let f := coefficient ρ hcont v v
  have hf : f ≠ 0 := by
    intro hz
    have hval := congrArg (fun F : C(SU2, ℂ) => F 1) hz
    have hvv : inner ℂ v v = 0 := by
      simpa only [f, coefficient_apply, action_one, ContinuousMap.zero_apply] using hval
    exact hv (inner_self_eq_zero.mp hvv)
  have hfLp : ContinuousMap.toLp 2 sourceHaar ℂ f ≠ 0 := by
    intro hz
    apply hf
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) sourceHaar
    simpa only [map_zero] using hz
  by_contra hn
  push Not at hn
  apply hfLp
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  rintro ⟨m, i, j⟩
  have hzero : average ρ hcont m (sourceBasis m j) v = 0 :=
    congrArg Representation.IntertwiningMap.toLinearMap
      (hn m (averageIntertwiner ρ hcont m (sourceBasis m j) v))
  have hint : (∫ U, conj (matrixEntry m i j U) * f U ∂sourceHaar) = 0 := by
    change (∫ U, conj (matrixCoefficient m (sourceBasis m i) (sourceBasis m j) U) *
      coefficient ρ hcont v v U ∂sourceHaar) = 0
    rw [coefficient_integral_eq_average, hzero]
    simp
  have hentry : inner ℂ (SourceCompleteCoefficients.entry m i j)
      (ContinuousMap.toLp 2 sourceHaar ℂ f) = 0 := by
    rw [SourceCompleteCoefficients.entry, ContinuousMap.inner_toLp]
    simpa only [mul_comm] using hint
  simp only [SourceCompleteCoefficients.basisVector, inner_smul_left,
    hentry, mul_zero, inner_zero_right]

omit [FiniteDimensional ℂ H] in
theorem intertwiner_apply {m : ℕ}
    (T : Representation.IntertwiningMap (hilbertRepresentation m) (linearRepresentation ρ))
    (U : SU2) (v : HilbertCarrier m) : T (unitaryAction m U v) = ρ U (T v) :=
  Representation.IntertwiningMap.isIntertwining _ _ T U v

/-- The Gram operator is an intertwiner because both actions preserve the
actual inner products, not because a metric is assigned to the intertwiner. -/
def gramIntertwiner {m : ℕ}
    (T : Representation.IntertwiningMap (hilbertRepresentation m) (linearRepresentation ρ)) :
    Representation.IntertwiningMap (hilbertRepresentation m) (hilbertRepresentation m) where
  toLinearMap := T.toLinearMap.adjoint.comp T.toLinearMap
  isIntertwining' U := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨z, rfl⟩ := (unitaryAction m U).surjective y
    change inner ℂ (unitaryAction m U z)
        (T.toLinearMap.adjoint (T (unitaryAction m U x))) =
      inner ℂ (unitaryAction m U z)
        (unitaryAction m U (T.toLinearMap.adjoint (T x)))
    calc
      _ = inner ℂ (T (unitaryAction m U z)) (T (unitaryAction m U x)) :=
        LinearMap.adjoint_inner_right T.toLinearMap _ _
      _ = inner ℂ (ρ U (T z)) (ρ U (T x)) :=
        congrArg₂ (inner ℂ) (intertwiner_apply ρ T U z) (intertwiner_apply ρ T U x)
      _ = inner ℂ (T z) (T x) := (ρ U).inner_map_map _ _
      _ = inner ℂ z (T.toLinearMap.adjoint (T x)) :=
        (LinearMap.adjoint_inner_right T.toLinearMap z (T x)).symm
      _ = _ := ((unitaryAction m U).inner_map_map _ _).symm

theorem intertwiner_inner_scalar {m : ℕ}
    (T : Representation.IntertwiningMap (hilbertRepresentation m) (linearRepresentation ρ)) :
    ∃ c : ℂ, ∀ x y : HilbertCarrier m, inner ℂ (T x) (T y) = c * inner ℂ x y := by
  let : Representation.IsIrreducible (hilbertRepresentation m) :=
    hilbertRepresentation_irreducible m
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := hilbertRepresentation m)).surjective (gramIntertwiner ρ T)
  have hgram (y : HilbertCarrier m) : T.toLinearMap.adjoint (T y) = c • y := by
    have hy := congrArg (fun F : Representation.IntertwiningMap
      (hilbertRepresentation m) (hilbertRepresentation m) => F y) hc
    simp only [Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.coe_smul, Representation.IntertwiningMap.coe_one,
      Pi.smul_apply, id_eq] at hy
    exact hy.symm
  refine ⟨c, fun x y => ?_⟩
  calc
    inner ℂ (T x) (T y) = inner ℂ x (T.toLinearMap.adjoint (T y)) :=
      (LinearMap.adjoint_inner_right T.toLinearMap x (T y)).symm
    _ = c * inner ℂ x y := by
      rw [hgram]
      exact inner_smul_right x y c

/-- A unitary equivalence which intertwines the actual source action with
the given representation. Its existence, not its uniqueness, is asserted. -/
def UnitaryIntertwiner (m : ℕ) :=
  { U : HilbertCarrier m ≃ₗᵢ[ℂ] H //
    ∀ g : SU2, ∀ v : HilbertCarrier m, U (unitaryAction m g v) = ρ g (U v) }

/-- A bijective source intertwiner has a positive normalization preserving
the given target inner product. -/
theorem unitaryIntertwiner_of_bijective {m : ℕ}
    (T : Representation.IntertwiningMap (hilbertRepresentation m) (linearRepresentation ρ))
    (hT : Function.Bijective T) : Nonempty (UnitaryIntertwiner ρ m) := by
  obtain ⟨c, hc⟩ := intertwiner_inner_scalar ρ T
  let e : HilbertCarrier m := sourceBasis m ⟨0, by omega⟩
  have heinner : inner ℂ e e = 1 := by
    exact orthonormal_iff_ite.mp (sourceBasis m).orthonormal _ _ |>.trans (ite_eq_left rfl)
  have he : e ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at heinner
    exact zero_ne_one heinner
  have hTe : T e ≠ 0 := by
    intro hz
    exact he (hT.injective (hz.trans (map_zero T).symm))
  let r : ℝ := ‖T e‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr hTe
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcvalue : c = (r : ℂ) ^ 2 := by
    have heq := hc e e
    rw [heinner, mul_one, inner_self_eq_norm_sq_to_K] at heq
    exact heq.symm
  let E : HilbertCarrier m ≃ₗ[ℂ] H := LinearEquiv.ofBijective T.toLinearMap hT
  let F : HilbertCarrier m ≃ₗ[ℂ] H :=
    E.trans (LinearEquiv.smulOfNeZero ℂ H ((r : ℂ)⁻¹) (inv_ne_zero hrC))
  have hF (x : HilbertCarrier m) : F x = (r : ℂ)⁻¹ • T x := rfl
  have hinner (x y : HilbertCarrier m) : inner ℂ (F x) (F y) = inner ℂ x y := by
    rw [hF, hF, inner_smul_left, inner_smul_right, hc, hcvalue]
    simp only [map_inv₀, Complex.conj_ofReal]
    field_simp [hrC]
  let U := F.isometryOfInner hinner
  refine ⟨⟨U, fun g x => ?_⟩⟩
  change F (unitaryAction m g x) = ρ g (F x)
  rw [hF, hF, intertwiner_apply, map_smul]

omit [FiniteDimensional ℂ H] in
theorem degree_eq_of_unitaryIntertwiner {m n : ℕ}
    (U : UnitaryIntertwiner ρ m) (V : UnitaryIntertwiner ρ n) : m = n := by
  have hd := (U.val.toLinearEquiv.trans V.val.symm.toLinearEquiv).finrank_eq
  rw [hilbertCarrier_finrank, hilbertCarrier_finrank] at hd
  exact Nat.succ.inj hd

include hcont in
/-- Every finite-dimensional continuous irreducible unitary representation
of the actual source group has exactly one homogeneous degree. -/
theorem exists_unique_degree
    [Representation.IsIrreducible (linearRepresentation ρ)] :
    ∃! m : ℕ, Nonempty (UnitaryIntertwiner ρ m) := by
  obtain ⟨m, T, hT⟩ := exists_nonzero_intertwiner ρ hcont
  let : Representation.IsIrreducible (hilbertRepresentation m) :=
    hilbertRepresentation_irreducible m
  have hbij : Function.Bijective T :=
    (Representation.IsIrreducible.bijective_or_eq_zero T).resolve_right hT
  obtain ⟨U⟩ := unitaryIntertwiner_of_bijective ρ T hbij
  refine ⟨m, ⟨U⟩, ?_⟩
  rintro n ⟨V⟩
  exact degree_eq_of_unitaryIntertwiner ρ V U

end GeneratedFoundations.Geometry.SourceIrreducibleClassification
