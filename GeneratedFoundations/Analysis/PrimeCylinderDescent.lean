module

public import GeneratedFoundations.Analysis.CanonicalEndpointLedger
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Prime-cylinder descent of the joint occupation--scale symmetry

The global prime flip acts simultaneously on occupation and scale.  This file
disintegrates that action over a fixed finite prime cylinder.  Adding a new
prime direction does not create an unrelated source: it combines the old
cylinder at scale `L` with the same cylinder at the forced scale `L / p`, with
the centre label reversed.  The resulting identities retain the complete
coherent cross term and make the central-potential dissipation theorem act on
the actual generated prime update.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.PrimeCylinderDescent

open GeneratedFoundations.Arithmetic.JointOccupationScale
open CanonicalEndpointLedger CenterEndpointPotential

/-- The scale forced by inserting a previously unoccupied prime while keeping
the dimensionless label-to-scale ratio fixed. -/
def dividedScale (p : PrimeIndex) (L : PositiveScale) : PositiveScale :=
  ⟨L.1 / (p.1 : ℝ), div_pos L.2 (Nat.cast_pos.mpr p.2.pos)⟩

theorem label_pos (nu : Occupation) : 0 < label nu := by
  unfold label
  exact Finset.prod_pos fun p _hp => p.2.pos

/-- The native endpoint difference is strictly positive on every generated
occupation and every positive scale. -/
theorem gaussianResponse_pos (nu : Occupation) (L : PositiveScale) :
    0 < gaussianResponse (nu, L) := by
  have hratio : 0 < ratio (nu, L) := by
    unfold ratio
    exact div_pos (by exact_mod_cast label_pos nu) L.2
  have hsq : 0 < ratio (nu, L) ^ 2 := sq_pos_of_pos hratio
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  unfold gaussianResponse
  rw [sub_pos, Real.exp_lt_exp]
  nlinarith [mul_lt_mul_of_pos_right hpi hsq]

theorem gaussianResponse_nonneg (nu : Occupation) (L : PositiveScale) :
    0 ≤ gaussianResponse (nu, L) := (gaussianResponse_pos nu L).le

/-- Inserting a new prime at scale `L` gives the old Gaussian response at the
forced scale `L / p`. -/
theorem gaussianResponse_insert (p : PrimeIndex) (nu : Occupation)
    (hp : p ∉ nu) (L : PositiveScale) :
    gaussianResponse (insert p nu, L) =
      gaussianResponse (nu, dividedScale p L) := by
  unfold gaussianResponse ratio dividedScale label
  rw [Finset.prod_insert hp]
  push_cast
  congr 1 <;> field_simp [Nat.ne_of_gt p.2.pos]

/-- A finite prime cylinder is the complete powerset of a finite set of prime
directions.  Its centre signs are summed before any square is formed. -/
def cylinderAmplitude (S : Finset PrimeIndex) (L : PositiveScale) : ℝ :=
  ∑ nu ∈ S.powerset,
    (centerCharacter nu : ℝ) * gaussianResponse (nu, L)

/-- The positive capacity carried by the same finite prime cylinder. -/
def cylinderCapacity (S : Finset PrimeIndex) (L : PositiveScale) : ℝ :=
  ∑ nu ∈ S.powerset, gaussianResponse (nu, L)

theorem cylinderCapacity_pos (S : Finset PrimeIndex) (L : PositiveScale) :
    0 < cylinderCapacity S L := by
  unfold cylinderCapacity
  exact Finset.sum_pos'
    (fun nu _hnu => gaussianResponse_nonneg nu L)
    ⟨∅, Finset.empty_mem_powerset S, gaussianResponse_pos ∅ L⟩

/-- The unique two-sector pair with the prescribed capacity and signed
amplitude. -/
def cylinderPair (S : Finset PrimeIndex) (L : PositiveScale) : CentrePair :=
  ⟨(cylinderCapacity S L + cylinderAmplitude S L) / 2,
    (cylinderCapacity S L - cylinderAmplitude S L) / 2⟩

@[simp] theorem cylinderPair_capacity (S : Finset PrimeIndex)
    (L : PositiveScale) :
    CentrePair.capacity (cylinderPair S L) = cylinderCapacity S L := by
  simp [cylinderPair, CentrePair.capacity]
  ring

@[simp] theorem cylinderPair_signed (S : Finset PrimeIndex)
    (L : PositiveScale) :
    CentrePair.signed (cylinderPair S L) = cylinderAmplitude S L := by
  simp [cylinderPair, CentrePair.signed]
  ring

/-- Inserting a new prime reverses the centre-labelled term and evaluates the
same old occupation at the forced scale. -/
theorem centerGaussian_insert (p : PrimeIndex) (nu : Occupation)
    (hp : p ∉ nu) (L : PositiveScale) :
    (centerCharacter (insert p nu) : ℝ) *
        gaussianResponse (insert p nu, L) =
      -((centerCharacter nu : ℝ) *
        gaussianResponse (nu, dividedScale p L)) := by
  rw [gaussianResponse_insert p nu hp L]
  simp only [centerCharacter, Finset.prod_insert hp]
  push_cast
  ring

/-- Exact fixed-scale descent of the global occupation--scale involution.
Every off-diagonal term generated after squaring this identity is retained. -/
theorem cylinderAmplitude_insert (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    cylinderAmplitude (insert p S) L =
      cylinderAmplitude S L - cylinderAmplitude S (dividedScale p L) := by
  rw [cylinderAmplitude, Finset.sum_powerset_insert hp]
  rw [cylinderAmplitude, cylinderAmplitude]
  have hterm : ∀ nu ∈ S.powerset,
      (centerCharacter (insert p nu) : ℝ) *
          gaussianResponse (insert p nu, L) =
        -((centerCharacter nu : ℝ) *
          gaussianResponse (nu, dividedScale p L)) := by
    intro nu hnu
    exact centerGaussian_insert p nu
      (Finset.notMem_mono (Finset.mem_powerset.mp hnu) hp) L
  calc
    (∑ nu ∈ S.powerset,
        (centerCharacter nu : ℝ) * gaussianResponse (nu, L)) +
        ∑ nu ∈ S.powerset,
          (centerCharacter (insert p nu) : ℝ) *
            gaussianResponse (insert p nu, L) =
      (∑ nu ∈ S.powerset,
        (centerCharacter nu : ℝ) * gaussianResponse (nu, L)) +
        ∑ nu ∈ S.powerset,
          -((centerCharacter nu : ℝ) *
            gaussianResponse (nu, dividedScale p L)) := by
              congr 1
              exact Finset.sum_congr rfl hterm
    _ = (∑ nu ∈ S.powerset,
        (centerCharacter nu : ℝ) * gaussianResponse (nu, L)) -
        ∑ nu ∈ S.powerset,
          (centerCharacter nu : ℝ) *
            gaussianResponse (nu, dividedScale p L) := by
              simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The corresponding positive capacity is the ordinary sum of the same two
scale copies. -/
theorem cylinderCapacity_insert (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    cylinderCapacity (insert p S) L =
      cylinderCapacity S L + cylinderCapacity S (dividedScale p L) := by
  rw [cylinderCapacity, Finset.sum_powerset_insert hp]
  rw [cylinderCapacity, cylinderCapacity]
  congr 1
  apply Finset.sum_congr rfl
  intro nu hnu
  exact gaussianResponse_insert p nu
    (Finset.notMem_mono (Finset.mem_powerset.mp hnu) hp) L

/-- At the level of the two positive centre sectors, a true prime birth is
exactly opposite-centre mixing of the old cylinder and its forced-scale copy. -/
theorem cylinderPair_insert (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    cylinderPair (insert p S) L =
      CentrePair.oppositeMix (cylinderPair S L)
        (cylinderPair S (dividedScale p L)) := by
  unfold cylinderPair CentrePair.oppositeMix CentrePair.add CentrePair.swap
  rw [cylinderCapacity_insert S p hp L,
    cylinderAmplitude_insert S p hp L]
  congr <;> ring

/-- Exact centre-potential ledger for one genuine prime-cylinder update.  The
only decrease is the explicit nonnegative mixing dissipation of the two forced
scale copies; no independent birth or fitted damping term is introduced. -/
theorem cylinderPotential_insert (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale)
    (hL : CentrePair.capacity (cylinderPair S L) ≠ 0)
    (hLp : CentrePair.capacity (cylinderPair S (dividedScale p L)) ≠ 0)
    (hsum : CentrePair.capacity (cylinderPair S L) +
        CentrePair.capacity (cylinderPair S (dividedScale p L)) ≠ 0) :
    CentrePair.quadraticPotential (cylinderPair (insert p S) L) =
      CentrePair.quadraticPotential (cylinderPair S L) +
      CentrePair.quadraticPotential (cylinderPair S (dividedScale p L)) -
      CentrePair.mixingDissipation (cylinderPair S L)
        (cylinderPair S (dividedScale p L)) := by
  rw [cylinderPair_insert S p hp L]
  linarith [CentrePair.quadraticPotential_mixing_identity
    (cylinderPair S L) (cylinderPair S (dividedScale p L)) hL hLp hsum]

/-- The actual prime-cylinder potential update has no nondegeneracy premise:
strict positivity of the native Gaussian source supplies every denominator. -/
theorem cylinderPotential_insert_unconditional
    (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    CentrePair.quadraticPotential (cylinderPair (insert p S) L) =
      CentrePair.quadraticPotential (cylinderPair S L) +
      CentrePair.quadraticPotential (cylinderPair S (dividedScale p L)) -
      CentrePair.mixingDissipation (cylinderPair S L)
        (cylinderPair S (dividedScale p L)) := by
  apply cylinderPotential_insert S p hp L
  · simpa using (cylinderCapacity_pos S L).ne'
  · simpa using (cylinderCapacity_pos S (dividedScale p L)).ne'
  · simp only [cylinderPair_capacity]
    exact (add_pos (cylinderCapacity_pos S L)
      (cylinderCapacity_pos S (dividedScale p L))).ne'

/-- The first genuine budget inequality in the fixed-scale descent.  It is a
direct consequence of the exact generated update and the nonnegative central
mixing loss; no term is estimated before the two scale copies are combined. -/
theorem cylinderPotential_insert_le
    (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    CentrePair.quadraticPotential (cylinderPair (insert p S) L) ≤
      CentrePair.quadraticPotential (cylinderPair S L) +
      CentrePair.quadraticPotential (cylinderPair S (dividedScale p L)) := by
  rw [cylinderPotential_insert_unconditional S p hp L]
  have hcapL : 0 ≤ CentrePair.capacity (cylinderPair S L) := by
    simpa using (cylinderCapacity_pos S L).le
  have hcapLp :
      0 ≤ CentrePair.capacity (cylinderPair S (dividedScale p L)) := by
    simpa using (cylinderCapacity_pos S (dividedScale p L)).le
  have hdiss := CentrePair.mixingDissipation_nonneg
    (cylinderPair S L) (cylinderPair S (dividedScale p L)) hcapL hcapLp
  linarith

/-- Squaring the exact amplitude descent exposes the complete old/returned
cross term rather than replacing it by an absolute-value estimate. -/
theorem cylinderEnergy_insert (S : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∉ S) (L : PositiveScale) :
    cylinderAmplitude (insert p S) L ^ 2 =
      cylinderAmplitude S L ^ 2 +
      cylinderAmplitude S (dividedScale p L) ^ 2 -
      2 * cylinderAmplitude S L *
        cylinderAmplitude S (dividedScale p L) := by
  rw [cylinderAmplitude_insert S p hp L]
  ring

/-- Bundled bridge from the global joint symmetry to fixed-scale prime
cylinders. -/
structure Conclusions : Prop where
  amplitude_descent : ∀ S p, p ∉ S → ∀ L,
    cylinderAmplitude (insert p S) L =
      cylinderAmplitude S L - cylinderAmplitude S (dividedScale p L)
  capacity_descent : ∀ S p, p ∉ S → ∀ L,
    cylinderCapacity (insert p S) L =
      cylinderCapacity S L + cylinderCapacity S (dividedScale p L)
  sector_descent : ∀ S p, p ∉ S → ∀ L,
    cylinderPair (insert p S) L =
      CentrePair.oppositeMix (cylinderPair S L)
        (cylinderPair S (dividedScale p L))
  coherent_energy_descent : ∀ S p, p ∉ S → ∀ L,
    cylinderAmplitude (insert p S) L ^ 2 =
      cylinderAmplitude S L ^ 2 +
      cylinderAmplitude S (dividedScale p L) ^ 2 -
      2 * cylinderAmplitude S L *
        cylinderAmplitude S (dividedScale p L)
  positive_capacity : ∀ S L, 0 < cylinderCapacity S L
  potential_descent : ∀ S p, p ∉ S → ∀ L,
    CentrePair.quadraticPotential (cylinderPair (insert p S) L) =
      CentrePair.quadraticPotential (cylinderPair S L) +
      CentrePair.quadraticPotential (cylinderPair S (dividedScale p L)) -
      CentrePair.mixingDissipation (cylinderPair S L)
        (cylinderPair S (dividedScale p L))
  potential_budget : ∀ S p, p ∉ S → ∀ L,
    CentrePair.quadraticPotential (cylinderPair (insert p S) L) ≤
      CentrePair.quadraticPotential (cylinderPair S L) +
      CentrePair.quadraticPotential (cylinderPair S (dividedScale p L))

theorem conclusions : Conclusions where
  amplitude_descent := cylinderAmplitude_insert
  capacity_descent := cylinderCapacity_insert
  sector_descent := cylinderPair_insert
  coherent_energy_descent := cylinderEnergy_insert
  positive_capacity := cylinderCapacity_pos
  potential_descent := cylinderPotential_insert_unconditional
  potential_budget := cylinderPotential_insert_le

end GeneratedFoundations.Analysis.PrimeCylinderDescent
