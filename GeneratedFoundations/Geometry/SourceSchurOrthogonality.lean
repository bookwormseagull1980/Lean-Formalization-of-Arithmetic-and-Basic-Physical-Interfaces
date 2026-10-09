module

public import GeneratedFoundations.Geometry.SourceSymmetricIrreducible
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Haar orthogonality of the actual homogeneous source coefficients

The source action is the continuous unitary realization of the original
homogeneous polynomial representation. A Haar average of actual orbit rank-one
maps is an intertwiner. Irreducibility and the proved dimensions distinguish
different degrees; in one degree Schur's lemma and a finite orthonormal trace
determine the scalar. No orthogonality assumption is used.

The statements concern every degree and arbitrary vectors in its actual
Hilbert carrier. They do not assert completeness of these coefficients in
the entire group function space or a classification of other representations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSymmetricIrreducible

namespace GeneratedFoundations.Geometry.SourceSchurOrthogonality

theorem action_mul (m : ℕ) (U V : SU2) (v : HilbertCarrier m) :
    unitaryAction m (U * V) v = unitaryAction m U (unitaryAction m V v) := by
  exact congrArg (fun e : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => e v)
    ((unitaryRepresentation m).map_mul U V)

/-- A coefficient of the actual Haar-orbit Hilbert realization. -/
def matrixCoefficient (m : ℕ) (v a : HilbertCarrier m) : C(SU2, ℂ) :=
  ⟨fun U => inner ℂ v (unitaryAction m U a),
    continuous_const.inner (unitaryAction_orbit_continuous m a)⟩

@[simp] theorem matrixCoefficient_apply (m : ℕ) (v a : HilbertCarrier m) (U : SU2) :
    matrixCoefficient m v a U = inner ℂ v (unitaryAction m U a) := rfl

theorem coefficient_product_integrable (m n : ℕ) (v a : HilbertCarrier m)
    (w b : HilbertCarrier n) :
    Integrable (fun U => conj (matrixCoefficient m v a U) * matrixCoefficient n w b U)
      sourceHaar :=
  (((matrixCoefficient m v a).continuous.star).mul
    (matrixCoefficient n w b).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- A rank-one map whose two vectors come from the same source operation. -/
def orbitRankOne (m n : ℕ) (a : HilbertCarrier m) (b : HilbertCarrier n)
    (v : HilbertCarrier m) (U : SU2) : HilbertCarrier n :=
  inner ℂ (unitaryAction m U a) v • unitaryAction n U b

theorem orbitRankOne_continuous (m n : ℕ) (a : HilbertCarrier m)
    (b : HilbertCarrier n) (v : HilbertCarrier m) :
    Continuous (orbitRankOne m n a b v) := by
  unfold orbitRankOne
  exact ((unitaryAction_orbit_continuous m a).inner (𝕜 := ℂ)
    (continuous_const (y := v))).smul (unitaryAction_orbit_continuous n b)

theorem orbitRankOne_integrable (m n : ℕ) (a : HilbertCarrier m)
    (b : HilbertCarrier n) (v : HilbertCarrier m) :
    Integrable (orbitRankOne m n a b v) sourceHaar :=
  (orbitRankOne_continuous m n a b v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The average is defined by its genuine vector-valued Haar integral. -/
def average (m n : ℕ) (a : HilbertCarrier m) (b : HilbertCarrier n) :
    HilbertCarrier m →ₗ[ℂ] HilbertCarrier n where
  toFun v := ∫ U, orbitRankOne m n a b v U ∂sourceHaar
  map_add' v w := by
    simp only [orbitRankOne, inner_add_right, add_smul]
    exact integral_add (orbitRankOne_integrable m n a b v)
      (orbitRankOne_integrable m n a b w)
  map_smul' c v := by
    simp only [orbitRankOne, inner_smul_right (𝕜 := ℂ), mul_smul, integral_smul,
      RingHom.id_apply]

@[simp] theorem average_apply (m n : ℕ) (a : HilbertCarrier m)
    (b : HilbertCarrier n) (v : HilbertCarrier m) :
    average m n a b v = ∫ U, orbitRankOne m n a b v U ∂sourceHaar := rfl

theorem orbitRankOne_translate (m n : ℕ) (a : HilbertCarrier m)
    (b : HilbertCarrier n) (v : HilbertCarrier m) (V U : SU2) :
    orbitRankOne m n a b (unitaryAction m V v) (V * U) =
      unitaryAction n V (orbitRankOne m n a b v U) := by
  simp only [orbitRankOne, action_mul, (unitaryAction m V).inner_map_map, map_smul]

/-- Left invariance of the normalized source Haar measure gives the intertwiner. -/
theorem average_intertwines (m n : ℕ) (a : HilbertCarrier m)
    (b : HilbertCarrier n) (V : SU2) (v : HilbertCarrier m) :
    average m n a b (unitaryAction m V v) = unitaryAction n V (average m n a b v) := by
  calc
    _ = ∫ U, orbitRankOne m n a b (unitaryAction m V v) (V * U) ∂sourceHaar :=
      (integral_mul_left_eq_self _ V).symm
    _ = ∫ U, unitaryAction n V (orbitRankOne m n a b v U) ∂sourceHaar := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact orbitRankOne_translate m n a b v V U
    _ = _ := (unitaryAction n V).toLinearIsometry.integral_comp_comm _

def averageIntertwiner (m n : ℕ) (a : HilbertCarrier m) (b : HilbertCarrier n) :
    Representation.IntertwiningMap (hilbertRepresentation m) (hilbertRepresentation n) where
  toLinearMap := average m n a b
  isIntertwining' U := by
    apply LinearMap.ext
    intro v
    exact average_intertwines m n a b U v

/-- The full coefficient-product integral is a matrix element of the average. -/
theorem coefficient_integral_eq_average (m n : ℕ) (v a : HilbertCarrier m)
    (w b : HilbertCarrier n) :
    (∫ U, conj (matrixCoefficient m v a U) * matrixCoefficient n w b U ∂sourceHaar) =
      inner ℂ w (average m n a b v) := by
  rw [average_apply, ← integral_inner (orbitRankOne_integrable m n a b v) w]
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [matrixCoefficient_apply, orbitRankOne, inner_conj_symm]
  exact (inner_smul_right w (unitaryAction n U b) _).symm

theorem average_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n)
    (a : HilbertCarrier m) (b : HilbertCarrier n) : average m n a b = 0 := by
  let : Representation.IsIrreducible (hilbertRepresentation m) :=
    hilbertRepresentation_irreducible m
  let : Representation.IsIrreducible (hilbertRepresentation n) :=
    hilbertRepresentation_irreducible n
  rcases Representation.IsIrreducible.bijective_or_eq_zero
      (averageIntertwiner m n a b) with hbij | hz
  · have hd := (LinearEquiv.ofBijective (average m n a b) hbij).finrank_eq
    rw [hilbertCarrier_finrank, hilbertCarrier_finrank] at hd
    exact False.elim (hmn (Nat.succ.inj hd))
  · exact congrArg Representation.IntertwiningMap.toLinearMap hz

/-- All matrix coefficients of distinct actual homogeneous degrees are orthogonal. -/
theorem matrixCoefficient_orthogonal_of_ne {m n : ℕ} (hmn : m ≠ n)
    (v a : HilbertCarrier m) (w b : HilbertCarrier n) :
    (∫ U, conj (matrixCoefficient m v a U) * matrixCoefficient n w b U ∂sourceHaar) = 0 := by
  rw [coefficient_integral_eq_average, average_eq_zero_of_ne hmn]
  simp

/-- This basis is in the actual orbit range, with its proved dimension. -/
def sourceBasis (m : ℕ) : OrthonormalBasis (Fin (m + 1)) ℂ (HilbertCarrier m) :=
  (stdOrthonormalBasis ℂ (HilbertCarrier m)).reindex (finCongr (hilbertCarrier_finrank m))

theorem average_trace (m : ℕ) (a b : HilbertCarrier m) :
    (∑ i : Fin (m + 1), inner ℂ (sourceBasis m i) (average m m a b (sourceBasis m i))) =
      inner ℂ a b := by
  calc
    _ = ∑ i : Fin (m + 1), ∫ U,
        inner ℂ (sourceBasis m i) (orbitRankOne m m a b (sourceBasis m i) U) ∂sourceHaar := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_inner (orbitRankOne_integrable m m a b (sourceBasis m i))
        (sourceBasis m i)).symm
    _ = ∫ U, ∑ i : Fin (m + 1),
        inner ℂ (sourceBasis m i) (orbitRankOne m m a b (sourceBasis m i) U) ∂sourceHaar :=
      (integral_finsetSum Finset.univ (fun i _ =>
        (orbitRankOne_integrable m m a b (sourceBasis m i)).const_inner (sourceBasis m i))).symm
    _ = ∫ _U : SU2, inner ℂ a b ∂sourceHaar := by
      apply integral_congr_ae
      filter_upwards [] with U
      calc
        _ = ∑ i : Fin (m + 1), inner ℂ (unitaryAction m U a) (sourceBasis m i) *
            inner ℂ (sourceBasis m i) (unitaryAction m U b) := by
          apply Finset.sum_congr rfl
          intro i _
          exact inner_smul_right (sourceBasis m i) (unitaryAction m U b) _
        _ = _ := ((sourceBasis m).sum_inner_mul_inner _ _).trans
          ((unitaryAction m U).inner_map_map a b)
    _ = _ := by simp

theorem average_exists_scalar (m : ℕ) (a b : HilbertCarrier m) :
    ∃ c : ℂ, ∀ v : HilbertCarrier m, average m m a b v = c • v := by
  let : Representation.IsIrreducible (hilbertRepresentation m) :=
    hilbertRepresentation_irreducible m
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := hilbertRepresentation m)).surjective (averageIntertwiner m m a b)
  refine ⟨c, fun v => ?_⟩
  have hv := congrArg (fun T : Representation.IntertwiningMap
    (hilbertRepresentation m) (hilbertRepresentation m) => T v) hc
  simp only [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.coe_smul, Representation.IntertwiningMap.coe_one,
    Pi.smul_apply, id_eq] at hv
  exact hv.symm

/-- The scalar is fixed by Haar mass one and the actual dimension `m+1`. -/
theorem average_apply_same (m : ℕ) (a b v : HilbertCarrier m) :
    average m m a b v = (inner ℂ a b / ((m + 1 : ℕ) : ℂ)) • v := by
  obtain ⟨c, hc⟩ := average_exists_scalar m a b
  have hinner (i : Fin (m + 1)) :
      inner ℂ (sourceBasis m i) (c • sourceBasis m i) = c := by
    calc
      _ = c * inner ℂ (sourceBasis m i) (sourceBasis m i) :=
        inner_smul_right (sourceBasis m i) (sourceBasis m i) c
      _ = c := by
        rw [orthonormal_iff_ite.mp (sourceBasis m).orthonormal, ite_eq_left rfl, mul_one]
  have htrace : ((m + 1 : ℕ) : ℂ) * c = inner ℂ a b := by
    rw [← average_trace m a b]
    simp only [hc, hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hscalar : c = inner ℂ a b / ((m + 1 : ℕ) : ℂ) := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using htrace
  rw [hc, hscalar]

/-- Schur's normalized formula for arbitrary actual source vectors. -/
theorem matrixCoefficient_integral_same (m : ℕ) (v a w b : HilbertCarrier m) :
    (∫ U, conj (matrixCoefficient m v a U) * matrixCoefficient m w b U ∂sourceHaar) =
      (inner ℂ a b / ((m + 1 : ℕ) : ℂ)) * inner ℂ w v := by
  rw [coefficient_integral_eq_average, average_apply_same]
  exact inner_smul_right w v _

/-- Matrix entries in an actual source Hilbert orthonormal basis. -/
def matrixEntry (m : ℕ) (i j : Fin (m + 1)) : C(SU2, ℂ) :=
  matrixCoefficient m (sourceBasis m i) (sourceBasis m j)

theorem matrixEntry_integral_same (m : ℕ) (i j k l : Fin (m + 1)) :
    (∫ U, conj (matrixEntry m i j U) * matrixEntry m k l U ∂sourceHaar) =
      if i = k ∧ j = l then (((m + 1 : ℕ) : ℂ))⁻¹ else 0 := by
  unfold matrixEntry
  rw [matrixCoefficient_integral_same]
  simp only [orthonormal_iff_ite.mp (sourceBasis m).orthonormal]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [hik, hjl, eq_comm]

theorem matrixEntry_integral_of_ne {m n : ℕ} (hmn : m ≠ n)
    (i j : Fin (m + 1)) (k l : Fin (n + 1)) :
    (∫ U, conj (matrixEntry m i j U) * matrixEntry n k l U ∂sourceHaar) = 0 :=
  matrixCoefficient_orthogonal_of_ne hmn _ _ _ _

end GeneratedFoundations.Geometry.SourceSchurOrthogonality
