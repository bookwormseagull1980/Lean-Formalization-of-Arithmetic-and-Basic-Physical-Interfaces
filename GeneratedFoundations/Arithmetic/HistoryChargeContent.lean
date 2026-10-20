module

public import GeneratedFoundations.Arithmetic.HistoryChargedReconstruction

/-!
# Content capacities of the complete arithmetic charge carrier

All counts are taken on the actual joint history--phase/source space. The
left projection is constructed there, while the charged rank is the rank
of its previously computed neutral quotient. The normalized squared-charge
capacity is identified with the trace of the actual response squared.

The resulting imbalance ratio keeps both the phase rank and the number of
histories. It is not assigned the value of a fixed physical carrier. The
formula at rank three and unit history multiplicity recovers that carrier's
numerical content ratio as an algebraic specialization.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryChargeContent

open HistoryJointCharge HistoryJointChargeLattice HistoryJointChargeQuotient

def historyCount (n : ℕ) : ℕ := Fintype.card (CompleteHistory.History (n + 1))

theorem historyCount_pos (n : ℕ) : 0 < historyCount n := Fintype.card_pos

def leftProjection (n : ℕ) : Module.End ℂ (Space n) :=
  blocks n (Sum.elim (fun _ => 1) (fun _ => 0))

theorem leftProjection_idempotent (n : ℕ) : IsIdempotentElem (leftProjection n) := by
  rw [IsIdempotentElem, leftProjection, blocks_mul]
  congr 1
  funext s
  cases s <;> simp

theorem leftProjection_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (leftProjection n) =
      (2 * historyCount n * (n + 1) : ℂ) := by
  rw [leftProjection, blocks_trace]
  simp [Fintype.sum_sum_type, Fibre,
    HistoryModuleRepresentation.Space, historyCount]
  ring

def leftCount (n : ℕ) : ℕ := Module.finrank ℂ (LinearMap.range (leftProjection n))

theorem leftCount_eq (n : ℕ) : leftCount n = 2 * historyCount n * (n + 1) := by
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (leftProjection_idempotent n)).trace
  rw [leftProjection_trace] at h
  exact_mod_cast h.symm

def chargedCount (n : ℕ) : ℕ := Module.finrank ℂ (Space n ⧸ neutral n)

theorem chargedCount_eq {n : ℕ} (hn : 2 ≤ n) :
    chargedCount n = (4 * n + 3) * historyCount n := charged_quotient_finrank hn

theorem left_neutral_zero {n : ℕ} (hn : 0 < n) :
    leftProjection n * neutralProjection n = 0 := by
  have hn' : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn.ne')
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  cases s <;>
    simp [Module.End.mul_apply, leftProjection, neutralProjection, blocks_apply,
      neutralComponent, generatedWeight, weight, rightWeight, relativeWeight, mask, hn']

theorem neutral_left_zero {n : ℕ} (hn : 0 < n) :
    neutralProjection n * leftProjection n = 0 := by
  have hn' : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn.ne')
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  cases s <;>
    simp [Module.End.mul_apply, leftProjection, neutralProjection, blocks_apply,
      neutralComponent, generatedWeight, weight, rightWeight, relativeWeight, mask, hn']

def rightChargedProjection (n : ℕ) : Module.End ℂ (Space n) :=
  1 - leftProjection n - neutralProjection n

theorem rightChargedProjection_idempotent {n : ℕ} (hn : 0 < n) :
    IsIdempotentElem (rightChargedProjection n) := by
  have hl : leftProjection n * leftProjection n = leftProjection n :=
    leftProjection_idempotent n
  have hp : neutralProjection n * neutralProjection n = neutralProjection n :=
    neutralProjection_idempotent n
  have hlp := left_neutral_zero hn
  have hpl := neutral_left_zero hn
  unfold rightChargedProjection
  change (1 - leftProjection n - neutralProjection n) *
    (1 - leftProjection n - neutralProjection n) = _
  noncomm_ring [hl, hp, hlp, hpl]

theorem rightChargedProjection_trace {n : ℕ} (hn : 2 ≤ n) :
    LinearMap.trace ℂ (Space n) (rightChargedProjection n) =
      ((2 * n + 1) * historyCount n : ℂ) := by
  rw [rightChargedProjection, map_sub, map_sub, LinearMap.trace_one,
    leftProjection_trace, neutral_trace_large hn, full_dimension]
  simp only [historyCount, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

def rightChargedCount (n : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (rightChargedProjection n))

theorem rightChargedCount_eq {n : ℕ} (hn : 2 ≤ n) :
    rightChargedCount n = (2 * n + 1) * historyCount n := by
  have hp : 0 < n := by omega
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (rightChargedProjection_idempotent hp)).trace
  rw [rightChargedProjection_trace hn] at h
  exact_mod_cast h.symm

theorem charged_count_balance {n : ℕ} (hn : 2 ≤ n) :
    chargedCount n = leftCount n + rightChargedCount n := by
  rw [chargedCount_eq hn, leftCount_eq, rightChargedCount_eq hn]
  ring

theorem full_reconstruction (n : ℕ) (x : Space n) :
    leftProjection n x + rightChargedProjection n x + neutralProjection n x = x := by
  simp [rightChargedProjection]
  abel

theorem imbalance_eq {n : ℕ} (hn : 2 ≤ n) :
    (leftCount n : ℚ) - rightChargedCount n = historyCount n := by
  rw [leftCount_eq, rightChargedCount_eq hn]
  push_cast
  ring

def normalizedResponse (n : ℕ) : Module.End ℂ (Space n) :=
  ((2 * n : ℂ)⁻¹) • generatedResponse n

def chargeSqSum (n : ℕ) : ℚ :=
  (2 * historyCount n * n * (n + 1) * (n + 2)) / (2 * n) ^ 2

theorem chargeSqSum_eq {n : ℕ} (hn : 0 < n) :
    chargeSqSum n = historyCount n * (n + 1) * (n + 2) / (2 * n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold chargeSqSum
  field_simp

theorem normalizedResponse_sq_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (normalizedResponse n * normalizedResponse n) =
      (chargeSqSum n : ℂ) := by
  rw [normalizedResponse, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_smul, response_sq_trace]
  simp only [smul_eq_mul, chargeSqSum, historyCount]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem chargeSqSum_pos {n : ℕ} (hn : 0 < n) : 0 < chargeSqSum n := by
  rw [chargeSqSum_eq hn]
  have hh : (0 : ℚ) < historyCount n := by exact_mod_cast historyCount_pos n
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  positivity

def contentRatio (n : ℕ) : ℚ :=
  ((leftCount n : ℚ) - rightChargedCount n) / (chargedCount n * chargeSqSum n)

theorem contentRatio_eq {n : ℕ} (hn : 2 ≤ n) :
    contentRatio n = (2 * n) /
      (historyCount n * (4 * n + 3) * (n + 1) * (n + 2)) := by
  have hp : 0 < n := by omega
  have hh : (historyCount n : ℚ) ≠ 0 := by exact_mod_cast (historyCount_pos n).ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [contentRatio, imbalance_eq hn, chargedCount_eq hn, chargeSqSum_eq hp]
  push_cast
  field_simp

theorem contentRatio_rank_three :
    contentRatio 3 = 1 / (50 * historyCount 3) := by
  rw [contentRatio_eq (by norm_num : 2 ≤ 3)]
  push_cast
  ring

structure Conclusions : Prop where
  actual_left_count : ∀ n, leftCount n = 2 * historyCount n * (n + 1)
  actual_quotient_count : ∀ n, 2 ≤ n → chargedCount n = (4 * n + 3) * historyCount n
  actual_imbalance : ∀ n, 2 ≤ n →
    (leftCount n : ℚ) - rightChargedCount n = historyCount n
  original_charge_trace : ∀ n,
    LinearMap.trace ℂ (Space n) (normalizedResponse n * normalizedResponse n) =
      (chargeSqSum n : ℂ)
  exact_ratio : ∀ n, 2 ≤ n → contentRatio n = (2 * n) /
    (historyCount n * (4 * n + 3) * (n + 1) * (n + 2))

theorem generated : Conclusions where
  actual_left_count := leftCount_eq
  actual_quotient_count := fun _ => chargedCount_eq
  actual_imbalance := fun _ => imbalance_eq
  original_charge_trace := normalizedResponse_sq_trace
  exact_ratio := fun _ => contentRatio_eq

end GeneratedFoundations.Arithmetic.HistoryChargeContent
