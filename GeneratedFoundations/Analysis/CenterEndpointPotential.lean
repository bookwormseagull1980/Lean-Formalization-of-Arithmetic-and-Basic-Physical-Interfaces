module

public import GeneratedFoundations.Analysis.SignedGaussianEnergy
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Positive endpoint sectors and the central quadratic potential

The natural Gaussian endpoint difference is positive before the arithmetic
sign is read.  This module separates that positive source into the two
generated Moebius sectors and proves that their difference is exactly the
finite signed endpoint response.

The second part is independent of a cutoff. It records the exact loss of the
quadratic central potential when a positive two-sector source is mixed with an
oppositely labelled source. This is the generated source--dissipation identity
for centre mixing and ordinary joining.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.CenterEndpointPotential

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedMobiusObservation
open SignedGaussianEnergy

/-- A positive source resolved into the two nonzero central sectors. -/
structure CentrePair where
  positive : ℝ
  negative : ℝ

namespace CentrePair

def capacity (x : CentrePair) : ℝ := x.positive + x.negative

def signed (x : CentrePair) : ℝ := x.positive - x.negative

def swap (x : CentrePair) : CentrePair :=
  ⟨x.negative, x.positive⟩

def add (x y : CentrePair) : CentrePair :=
  ⟨x.positive + y.positive, x.negative + y.negative⟩

/-- Addition after reversing the central label on the second source. -/
def oppositeMix (x y : CentrePair) : CentrePair := add x (swap y)

/-- Normalized central bias. -/
def bias (x : CentrePair) : ℝ := signed x / capacity x

/-- The quadratic proxy for the non-normalized binary relative potential. -/
def quadraticPotential (x : CentrePair) : ℝ :=
  signed x ^ 2 / capacity x

/-- Exact positive loss of the quadratic central potential under opposite
mixing. -/
def mixingDissipation (x y : CentrePair) : ℝ :=
  capacity x * capacity y / (capacity x + capacity y) *
    (bias x + bias y) ^ 2

/-- Exact loss of the quadratic central potential when two sources carrying
the same central labelling are joined. -/
def joinDissipation (x y : CentrePair) : ℝ :=
  capacity x * capacity y / (capacity x + capacity y) *
    (bias x - bias y) ^ 2

@[simp] theorem capacity_swap (x : CentrePair) :
    capacity (swap x) = capacity x := by
  simp [capacity, swap, add_comm]

@[simp] theorem signed_swap (x : CentrePair) :
    signed (swap x) = -signed x := by
  simp [signed, swap]

@[simp] theorem capacity_add (x y : CentrePair) :
    capacity (add x y) = capacity x + capacity y := by
  simp [capacity, add]
  ring

@[simp] theorem signed_add (x y : CentrePair) :
    signed (add x y) = signed x + signed y := by
  simp [signed, add]
  ring

@[simp] theorem capacity_oppositeMix (x y : CentrePair) :
    capacity (oppositeMix x y) = capacity x + capacity y := by
  simp [oppositeMix]

@[simp] theorem signed_oppositeMix (x y : CentrePair) :
    signed (oppositeMix x y) = signed x - signed y := by
  simp [oppositeMix]
  ring

theorem capacity_nonneg (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    0 ≤ capacity x := by
  exact add_nonneg hpos hneg

theorem signed_sq_le_capacity_sq (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    signed x ^ 2 ≤ capacity x ^ 2 := by
  simp only [signed, capacity]
  nlinarith [mul_nonneg hpos hneg]

theorem quadraticPotential_nonneg (x : CentrePair)
    (hcap : 0 ≤ capacity x) :
    0 ≤ quadraticPotential x := by
  exact div_nonneg (sq_nonneg _) hcap

/-- The central mixing identity.  It is the exact quadratic counterpart of
the binary relative-entropy chain rule. -/
theorem quadraticPotential_mixing_identity (x y : CentrePair)
    (hx : capacity x ≠ 0) (hy : capacity y ≠ 0)
    (hxy : capacity x + capacity y ≠ 0) :
    quadraticPotential x + quadraticPotential y -
        quadraticPotential (oppositeMix x y) =
      mixingDissipation x y := by
  simp only [quadraticPotential, mixingDissipation, bias,
    capacity_oppositeMix, signed_oppositeMix]
  field_simp [hx, hy, hxy]
  ring

/-- The ordinary joining identity.  Unlike `oppositeMix`, no central label is
reversed, so the dissipated square contains the difference of the two biases. -/
theorem quadraticPotential_join_identity (x y : CentrePair)
    (hx : capacity x ≠ 0) (hy : capacity y ≠ 0)
    (hxy : capacity x + capacity y ≠ 0) :
    quadraticPotential x + quadraticPotential y -
        quadraticPotential (add x y) =
      joinDissipation x y := by
  simp only [quadraticPotential, joinDissipation, bias,
    capacity_add, signed_add]
  field_simp [hx, hy, hxy]
  ring

theorem mixingDissipation_nonneg (x y : CentrePair)
    (hx : 0 ≤ capacity x) (hy : 0 ≤ capacity y) :
    0 ≤ mixingDissipation x y := by
  unfold mixingDissipation
  exact mul_nonneg
    (div_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)) (sq_nonneg _)

theorem joinDissipation_nonneg (x y : CentrePair)
    (hx : 0 ≤ capacity x) (hy : 0 ≤ capacity y) :
    0 ≤ joinDissipation x y := by
  unfold joinDissipation
  exact mul_nonneg
    (div_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)) (sq_nonneg _)

/-- One exact finite generation stage: first mix an old source with an
oppositely labelled source, then join the legal birth source.  Both favourable
losses and the full birth potential remain visible. -/
theorem oppositeMix_then_birth_ledger (x y birth : CentrePair)
    (hx : capacity x ≠ 0) (hy : capacity y ≠ 0)
    (hxy : capacity x + capacity y ≠ 0)
    (hbirth : capacity birth ≠ 0)
    (hnext : capacity x + capacity y + capacity birth ≠ 0) :
    quadraticPotential (add (oppositeMix x y) birth) =
      quadraticPotential x + quadraticPotential y +
        quadraticPotential birth - mixingDissipation x y -
        joinDissipation (oppositeMix x y) birth := by
  have hmix := quadraticPotential_mixing_identity x y hx hy hxy
  have hmixcap : capacity (oppositeMix x y) ≠ 0 := by
    simpa using hxy
  have hnextcap : capacity (oppositeMix x y) + capacity birth ≠ 0 := by
    simpa [add_assoc] using hnext
  have hjoin := quadraticPotential_join_identity (oppositeMix x y) birth
    hmixcap hbirth hnextcap
  linarith

end CentrePair

/-- Difference of the two intrinsic Gaussian endpoint masses. -/
def endpointWeight (L : ℝ) (n : ℕ) : ℝ :=
  gaussianRootMass 1 L n - gaussianRootMass Real.pi L n

theorem endpointWeight_nonneg (L : ℝ) (n : ℕ) :
    0 ≤ endpointWeight L n := by
  unfold endpointWeight gaussianRootMass
  apply sub_nonneg.mpr
  rw [Real.exp_le_exp]
  have hq : 0 ≤ (n : ℝ) ^ 2 / L ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hpi hq)
  convert hneg using 1 <;> ring

/-- Positive mass in the generated `+1` central sector. -/
def positiveSectorMass (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, if generatedMoebius n = 1 then w n else 0

/-- Positive mass in the generated `-1` central sector. -/
def negativeSectorMass (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, if generatedMoebius n = -1 then w n else 0

def sectorPair (w : ℕ → ℝ) (N : ℕ) : CentrePair :=
  ⟨positiveSectorMass w N, negativeSectorMass w N⟩

/-- The signed observation before any square or absolute value. -/
def finiteSignedResponse (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, (generatedMoebius n : ℝ) * w n

/-- The positive squarefree support capacity of the same source. -/
def finiteSupportCapacity (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, (squarefreeProjector n : ℝ) * w n

private theorem generatedMoebius_eq_zero_or_one_or_neg_one (n : ℕ) :
    generatedMoebius n = 0 ∨ generatedMoebius n = 1 ∨
      generatedMoebius n = -1 := by
  simpa only [generatedMoebius_eq_moebius] using
    ArithmeticFunction.moebius_eq_or n

theorem sectorPair_signed (w : ℕ → ℝ) (N : ℕ) :
    CentrePair.signed (sectorPair w N) = finiteSignedResponse w N := by
  change positiveSectorMass w N - negativeSectorMass w N =
    finiteSignedResponse w N
  rw [finiteSignedResponse, positiveSectorMass, negativeSectorMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rcases generatedMoebius_eq_zero_or_one_or_neg_one n with hn | hn | hn <;>
    simp [hn]

theorem sectorPair_capacity (w : ℕ → ℝ) (N : ℕ) :
    CentrePair.capacity (sectorPair w N) = finiteSupportCapacity w N := by
  change positiveSectorMass w N + negativeSectorMass w N =
    finiteSupportCapacity w N
  rw [finiteSupportCapacity, positiveSectorMass, negativeSectorMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hsquare : ((generatedMoebius n : ℝ) ^ 2) =
      (squarefreeProjector n : ℝ) := by
    norm_cast
    exact generatedMoebius_sq n
  rw [← hsquare]
  rcases generatedMoebius_eq_zero_or_one_or_neg_one n with hn | hn | hn <;>
    simp [hn]

theorem positiveSectorMass_nonneg (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n ∈ rootRange N, 0 ≤ w n) :
    0 ≤ positiveSectorMass w N := by
  apply Finset.sum_nonneg
  intro n hn
  split <;> simp [hw n hn]

theorem negativeSectorMass_nonneg (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n ∈ rootRange N, 0 ≤ w n) :
    0 ≤ negativeSectorMass w N := by
  apply Finset.sum_nonneg
  intro n hn
  split <;> simp [hw n hn]

theorem endpoint_sectorPair_nonnegative (L : ℝ) (N : ℕ) :
    0 ≤ (sectorPair (endpointWeight L) N).positive ∧
      0 ≤ (sectorPair (endpointWeight L) N).negative := by
  constructor
  · exact positiveSectorMass_nonneg (endpointWeight L) N
      (fun n _ => endpointWeight_nonneg L n)
  · exact negativeSectorMass_nonneg (endpointWeight L) N
      (fun n _ => endpointWeight_nonneg L n)

/-- The endpoint source, its exact central-sector resolution and its exact
mixing and joining ledgers. -/
structure Conclusions : Prop where
  endpoint_positive : ∀ (L : ℝ) (n : ℕ), 0 ≤ endpointWeight L n
  signed_resolution : ∀ (w : ℕ → ℝ) (N : ℕ),
    CentrePair.signed (sectorPair w N) = finiteSignedResponse w N
  capacity_resolution : ∀ (w : ℕ → ℝ) (N : ℕ),
    CentrePair.capacity (sectorPair w N) = finiteSupportCapacity w N
  mixing_identity : ∀ (x y : CentrePair),
    CentrePair.capacity x ≠ 0 → CentrePair.capacity y ≠ 0 →
      CentrePair.capacity x + CentrePair.capacity y ≠ 0 →
      CentrePair.quadraticPotential x + CentrePair.quadraticPotential y -
          CentrePair.quadraticPotential (CentrePair.oppositeMix x y) =
        CentrePair.mixingDissipation x y
  join_identity : ∀ (x y : CentrePair),
    CentrePair.capacity x ≠ 0 → CentrePair.capacity y ≠ 0 →
      CentrePair.capacity x + CentrePair.capacity y ≠ 0 →
      CentrePair.quadraticPotential x + CentrePair.quadraticPotential y -
          CentrePair.quadraticPotential (CentrePair.add x y) =
        CentrePair.joinDissipation x y
  stage_ledger : ∀ (x y birth : CentrePair),
    CentrePair.capacity x ≠ 0 → CentrePair.capacity y ≠ 0 →
      CentrePair.capacity x + CentrePair.capacity y ≠ 0 →
      CentrePair.capacity birth ≠ 0 →
      CentrePair.capacity x + CentrePair.capacity y +
          CentrePair.capacity birth ≠ 0 →
      CentrePair.quadraticPotential
          (CentrePair.add (CentrePair.oppositeMix x y) birth) =
        CentrePair.quadraticPotential x + CentrePair.quadraticPotential y +
          CentrePair.quadraticPotential birth -
          CentrePair.mixingDissipation x y -
          CentrePair.joinDissipation (CentrePair.oppositeMix x y) birth

theorem centerEndpointPotentialConclusions : Conclusions where
  endpoint_positive := endpointWeight_nonneg
  signed_resolution := sectorPair_signed
  capacity_resolution := sectorPair_capacity
  mixing_identity := CentrePair.quadraticPotential_mixing_identity
  join_identity := CentrePair.quadraticPotential_join_identity
  stage_ledger := CentrePair.oppositeMix_then_birth_ledger

end GeneratedFoundations.Analysis.CenterEndpointPotential
