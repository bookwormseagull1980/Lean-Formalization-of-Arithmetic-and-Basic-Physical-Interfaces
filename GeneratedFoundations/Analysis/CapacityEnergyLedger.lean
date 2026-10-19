module

public import GeneratedFoundations.Analysis.CanonicalEndpointLedger
public import GeneratedFoundations.Analysis.MaximumPrimeFactorStage
public import GeneratedFoundations.Analysis.CenterRelativePotential
public import GeneratedFoundations.Analysis.PrimeCapacity

/-!
# Capacity-weighted energy of the generated centre sectors

For a nonnegative sector pair the coherent energy is `B^2 = C * V`, where
`V = B^2 / C`. This identity includes empty sectors. The distinction between
energy and potential matters when a genuine prime birth changes the capacity.

The joining formula below retains the capacity increment, the returned
source and the complete signed cross term. Its prime-stage specialization
uses the actual generated birth set and its natural cutoff.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.CapacityEnergyLedger

open CenterEndpointPotential MaximumPrimeFactorStage
open CanonicalMobiusReadout CanonicalEndpointLedger
open GeneratedFoundations.Arithmetic.JointOccupationScale

/-- Coherent energy after the two sector responses have been combined. -/
def coherentEnergy (x : CentrePair) : ℝ := CentrePair.signed x ^ 2

/-- Capacity in the direction transverse to the signed centre observation. -/
def transverseCapacity (x : CentrePair) : ℝ :=
  CentrePair.capacity x - CentrePair.quadraticPotential x

/-- Nonnegative sectors of zero total capacity have zero signed response. -/
theorem signed_eq_zero_of_capacity_eq_zero (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative)
    (hzero : CentrePair.capacity x = 0) : CentrePair.signed x = 0 := by
  dsimp [CentrePair.capacity] at hzero
  dsimp [CentrePair.signed]
  linarith

/-- Exact energy reconstruction, including the empty source. -/
theorem capacity_mul_potential_eq_coherentEnergy (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    CentrePair.capacity x * CentrePair.quadraticPotential x =
      coherentEnergy x := by
  by_cases hzero : CentrePair.capacity x = 0
  · have hs := signed_eq_zero_of_capacity_eq_zero x hpos hneg hzero
    simp [coherentEnergy, CentrePair.quadraticPotential, hzero, hs]
  · unfold CentrePair.quadraticPotential coherentEnergy
    field_simp [hzero]

/-- Longitudinal and transverse capacities resolve the same positive source. -/
theorem potential_add_transverse (x : CentrePair) :
    CentrePair.quadraticPotential x + transverseCapacity x =
      CentrePair.capacity x := by
  unfold transverseCapacity
  ring

theorem transverseCapacity_nonneg (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    0 ≤ transverseCapacity x := by
  have hcap := CentrePair.capacity_nonneg x hpos hneg
  by_cases hzero : CentrePair.capacity x = 0
  · simp [transverseCapacity, CentrePair.quadraticPotential, hzero]
  · have hpositive : 0 < CentrePair.capacity x := lt_of_le_of_ne hcap (Ne.symm hzero)
    have hs := CentrePair.signed_sq_le_capacity_sq x hpos hneg
    have hdiv : CentrePair.quadraticPotential x ≤ CentrePair.capacity x := by
      rw [CentrePair.quadraticPotential, div_le_iff₀ hpositive]
      nlinarith
    exact sub_nonneg.mpr hdiv

/-- The positive capacity record is obtained from the actual centre sectors;
no replacement of their signs or weights is made. -/
def toCapacityPair (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative)
    (hcap : 0 < CentrePair.capacity x) : PrimeCapacity.CapacityPair where
  plus := x.positive
  minus := x.negative
  plus_nonneg := hpos
  minus_nonneg := hneg
  total_pos := hcap

theorem toCapacityPair_transverse (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative)
    (hcap : 0 < CentrePair.capacity x) :
    (toCapacityPair x hpos hneg hcap).transverse = transverseCapacity x := rfl

/-- The relative-potential comparison retains the factor of the actual
capacity when it is converted to coherent energy. -/
theorem coherentEnergy_le_capacity_mul_relativePotential (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    coherentEnergy x ≤
      2 * CentrePair.capacity x * CenterRelativePotential.relativePotential x := by
  have h := mul_le_mul_of_nonneg_left
    (CenterRelativePotential.half_quadraticPotential_le_relativePotential x hpos hneg)
    (CentrePair.capacity_nonneg x hpos hneg)
  have he := capacity_mul_potential_eq_coherentEnergy x hpos hneg
  nlinarith

/-- Ordinary joining preserves the complete coherent cross term. -/
theorem coherentEnergy_add (x y : CentrePair) :
    coherentEnergy (CentrePair.add x y) =
      coherentEnergy x + coherentEnergy y +
        2 * CentrePair.signed x * CentrePair.signed y := by
  simp only [coherentEnergy, CentrePair.signed_add]
  ring

/-- Capacity-weighted joining ledger. In contrast with the normalized
potential identity, the old potential also carries the new capacity. -/
theorem coherentEnergy_add_increment (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative) :
    coherentEnergy (CentrePair.add x y) - coherentEnergy x =
      CentrePair.capacity y * CentrePair.quadraticPotential x +
        (CentrePair.capacity x + CentrePair.capacity y) *
          CentrePair.quadraticPotential y -
        (CentrePair.capacity x + CentrePair.capacity y) *
          CentrePair.joinDissipation x y := by
  have hx := capacity_mul_potential_eq_coherentEnergy x hxpos hxneg
  have hy := capacity_mul_potential_eq_coherentEnergy y hypos hyneg
  have hsumpos : 0 ≤ (CentrePair.add x y).positive := add_nonneg hxpos hypos
  have hsumneg : 0 ≤ (CentrePair.add x y).negative := add_nonneg hxneg hyneg
  have hsum := capacity_mul_potential_eq_coherentEnergy
    (CentrePair.add x y) hsumpos hsumneg
  have hjoin := quadraticPotential_join_identity_nonnegative
    x y hxpos hxneg hypos hyneg
  rw [CentrePair.capacity_add] at hsum
  nlinarith [congrArg (fun z : ℝ =>
    (CentrePair.capacity x + CentrePair.capacity y) * z) hjoin]

/-- The capacity increment of an actual prime birth is the positive capacity
of the returned old source at the transported observation scale. -/
theorem generated_stage_capacity_increment (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    CentrePair.capacity (sectorPairOn w (stageAfter p N)) =
      CentrePair.capacity (beforePair w p N) +
        CentrePair.capacity (returnPair w p N) := by
  rw [stageAfter, sectorPairOn_union w (disjoint_stageBefore_stageBirth hp),
    sectorPairOn_stageBirth_eq_birthPair w hp]
  simp [beforePair, birthPair]

/-- Full coherent energy ledger for the genuine generated stage. The
capacity increase and the signed old--birth interaction are both retained. -/
theorem generated_stage_coherentEnergy_increment (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) (hw : ∀ n, 0 ≤ w n) :
    coherentEnergy (sectorPairOn w (stageAfter p N)) -
        coherentEnergy (beforePair w p N) =
      CentrePair.capacity (returnPair w p N) *
          CentrePair.quadraticPotential (beforePair w p N) +
        (CentrePair.capacity (beforePair w p N) +
          CentrePair.capacity (returnPair w p N)) *
          CentrePair.quadraticPotential (returnPair w p N) -
        (CentrePair.capacity (beforePair w p N) +
          CentrePair.capacity (returnPair w p N)) *
          CentrePair.joinDissipation (beforePair w p N) (birthPair w p N) := by
  have hold := sectorPairOn_nonnegative w (stageBefore p N) (fun n _ => hw n)
  have hreturn := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _ => hw (p * n))
  have h := coherentEnergy_add_increment (beforePair w p N) (birthPair w p N)
    hold.1 hold.2 hreturn.2 hreturn.1
  rw [stageAfter, sectorPairOn_union w (disjoint_stageBefore_stageBirth hp),
    sectorPairOn_stageBirth_eq_birthPair w hp]
  simpa only [beforePair, birthPair, CentrePair.capacity_swap,
    quadraticPotential_swap] using h

/-- The same exact energy increment in its signed-correlation coordinate. -/
theorem generated_stage_coherentEnergy_correlation (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    coherentEnergy (sectorPairOn w (stageAfter p N)) -
        coherentEnergy (beforePair w p N) =
      coherentEnergy (returnPair w p N) -
        2 * CentrePair.signed (beforePair w p N) *
          CentrePair.signed (returnPair w p N) := by
  rw [stageAfter, sectorPairOn_union w (disjoint_stageBefore_stageBirth hp),
    sectorPairOn_stageBirth_eq_birthPair w hp, coherentEnergy_add]
  simp only [birthPair, coherentEnergy, CentrePair.signed_swap]
  change (CentrePair.signed (beforePair w p N) ^ 2 +
    (-CentrePair.signed (returnPair w p N)) ^ 2 +
    2 * CentrePair.signed (beforePair w p N) *
      (-CentrePair.signed (returnPair w p N))) - _ = _
  ring

/-- Empty natural prefixes are included in the canonical endpoint identity. -/
theorem canonical_energy_reconstruction (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (canonicalEndpointPair L N) *
        CentrePair.quadraticPotential (canonicalEndpointPair L N) =
      canonicalOccupationEnergy L N := by
  obtain ⟨hp, hn⟩ := canonicalEndpointPair_nonnegative L N
  have h := capacity_mul_potential_eq_coherentEnergy
    (canonicalEndpointPair L N) hp hn
  simpa only [coherentEnergy, canonicalEndpointPair_signed,
    canonicalOccupationEnergy] using h

end GeneratedFoundations.Analysis.CapacityEnergyLedger
