module

public import GeneratedFoundations.Analysis.CanonicalMobiusReadout
public import GeneratedFoundations.Analysis.CenterEndpointPotential

/-!
# Canonical endpoint ledger for the generated arithmetic source

The native two-endpoint Gaussian window, the positive centre-sector source,
the generated Mobius response and the coherent quadratic energy are four
coordinates of one object. This module proves their exact compatibility.

The centre signs are read only after the positive source has been resolved
into its two intrinsic sectors, and the signed amplitudes are combined before
the energy is formed. Consequently every diagonal and off-diagonal term of
the generated coherent energy is retained by the endpoint ledger.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.CanonicalEndpointLedger

open GeneratedFoundations.Arithmetic.JointOccupationScale
open CanonicalMobiusReadout CenterEndpointPotential

theorem gaussianWindowMass_eq_endpointWeight (L : ℝ) (n : ℕ) :
    gaussianWindowMass L n = endpointWeight L n := rfl

/-- The positive endpoint source resolved by its generated centre character. -/
def canonicalEndpointPair (L : PositiveScale) (N : ℕ) : CentrePair :=
  sectorPair (gaussianWindowMass L.1) N

theorem canonicalEndpointPair_nonnegative (L : PositiveScale) (N : ℕ) :
    0 ≤ (canonicalEndpointPair L N).positive ∧
      0 ≤ (canonicalEndpointPair L N).negative := by
  constructor
  · exact positiveSectorMass_nonneg (gaussianWindowMass L.1) N
      (fun n _ => by
        rw [gaussianWindowMass_eq_endpointWeight]
        exact endpointWeight_nonneg L.1 n)
  · exact negativeSectorMass_nonneg (gaussianWindowMass L.1) N
      (fun n _ => by
        rw [gaussianWindowMass_eq_endpointWeight]
        exact endpointWeight_nonneg L.1 n)

/-- The centre difference of the positive endpoint source is exactly the
canonical finite Mobius--Gaussian amplitude. -/
theorem canonicalEndpointPair_signed (L : PositiveScale) (N : ℕ) :
    CentrePair.signed (canonicalEndpointPair L N) =
      canonicalOccupationAmplitude L N := by
  calc
    CentrePair.signed (canonicalEndpointPair L N) =
        finiteSignedResponse (gaussianWindowMass L.1) N :=
      sectorPair_signed (gaussianWindowMass L.1) N
    _ = rootMobiusWindowAmplitude L N := rfl
    _ = canonicalOccupationAmplitude L N :=
      (canonicalOccupationAmplitude_eq_root L N).symm

/-- The centre capacity is the positive squarefree support of the same
endpoint source. -/
theorem canonicalEndpointPair_capacity (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (canonicalEndpointPair L N) =
      finiteSupportCapacity (gaussianWindowMass L.1) N :=
  sectorPair_capacity (gaussianWindowMass L.1) N

/-- Capacity times central quadratic potential reconstructs the complete
coherent endpoint energy exactly. -/
theorem capacity_mul_potential_eq_energy (L : PositiveScale) (N : ℕ)
    (hcap : CentrePair.capacity (canonicalEndpointPair L N) ≠ 0) :
    CentrePair.capacity (canonicalEndpointPair L N) *
        CentrePair.quadraticPotential (canonicalEndpointPair L N) =
      canonicalOccupationEnergy L N := by
  rw [CentrePair.quadraticPotential]
  field_simp [hcap]
  rw [canonicalEndpointPair_signed]
  rfl

/-- The coherent energy is bounded by the square of the positive capacity of
the very same endpoint source. -/
theorem coherentEnergy_le_capacity_sq (L : PositiveScale) (N : ℕ) :
    canonicalOccupationEnergy L N ≤
      finiteSupportCapacity (gaussianWindowMass L.1) N ^ 2 := by
  obtain ⟨hpos, hneg⟩ := canonicalEndpointPair_nonnegative L N
  have h := CentrePair.signed_sq_le_capacity_sq
    (canonicalEndpointPair L N) hpos hneg
  simpa [canonicalOccupationEnergy, canonicalEndpointPair_signed,
    canonicalEndpointPair_capacity] using h

/-- The canonical occupation descent and the endpoint centre ledger form one
exact generated arithmetic output. -/
structure Conclusions : Prop where
  endpoint_identity : ∀ (L : ℝ) (n : ℕ),
    gaussianWindowMass L n = endpointWeight L n
  positive_sectors : ∀ (L : PositiveScale) (N : ℕ),
    0 ≤ (canonicalEndpointPair L N).positive ∧
      0 ≤ (canonicalEndpointPair L N).negative
  signed_readout : ∀ (L : PositiveScale) (N : ℕ),
    CentrePair.signed (canonicalEndpointPair L N) =
      canonicalOccupationAmplitude L N
  capacity_readout : ∀ (L : PositiveScale) (N : ℕ),
    CentrePair.capacity (canonicalEndpointPair L N) =
      finiteSupportCapacity (gaussianWindowMass L.1) N
  exact_energy : ∀ (L : PositiveScale) (N : ℕ),
    CentrePair.capacity (canonicalEndpointPair L N) ≠ 0 →
      CentrePair.capacity (canonicalEndpointPair L N) *
          CentrePair.quadraticPotential (canonicalEndpointPair L N) =
        canonicalOccupationEnergy L N
  capacity_control : ∀ (L : PositiveScale) (N : ℕ),
    canonicalOccupationEnergy L N ≤
      finiteSupportCapacity (gaussianWindowMass L.1) N ^ 2
  centre_ledger : CenterEndpointPotential.Conclusions

theorem conclusions : Conclusions where
  endpoint_identity := gaussianWindowMass_eq_endpointWeight
  positive_sectors := canonicalEndpointPair_nonnegative
  signed_readout := canonicalEndpointPair_signed
  capacity_readout := canonicalEndpointPair_capacity
  exact_energy := capacity_mul_potential_eq_energy
  capacity_control := coherentEnergy_le_capacity_sq
  centre_ledger := centerEndpointPotentialConclusions

end GeneratedFoundations.Analysis.CanonicalEndpointLedger
