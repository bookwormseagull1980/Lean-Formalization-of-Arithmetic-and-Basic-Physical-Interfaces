module

public import GeneratedFoundations.Arithmetic.HistoryHaarJointHessian
public import GeneratedFoundations.Arithmetic.HistoryCentreNormalization
public import GeneratedFoundations.Arithmetic.HistoryHermitianBasis

/-!
# Actual response capacities and exact spectral certificates

The connection coefficient count uses the complete arithmetic coordinate
set and an independent Hermitian traceless basis. The positive joint gap is
the bottom of the already constructed closed Haar/state Hessian. Its
dimensionless square root is uniquely determined and has exact uniform
bounds. Interval consumption below is an implication checked in Lean;
these exact bounds themselves require no external numerical certificate.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryResponseCertificates

def coefficientCount (N : ℕ) : ℕ :=
  Fintype.card (HistoryGaugeJets.CoordinateIndex N) *
    Fintype.card (HistoryHermitianBasis.GeneratorIndex N)

theorem coefficientCount_eq (N : ℕ) : coefficientCount N =
    Fintype.card (HistoryGaugeJets.CoordinateIndex N) *
      (HistoryAdjointCasimir.dimension N ^ 2 - 1) := by
  rw [coefficientCount, HistoryHermitianBasis.generator_count]

theorem coefficientCount_pos (N : ℕ) : 0 < coefficientCount N := by
  have hh : 0 < Fintype.card (HistoryGaugeJets.CoordinateIndex N) :=
    Fintype.card_pos_iff.mpr ⟨HistoryCliffordAction.historyPoint N⟩
  have hd := HistoryAdjointCasimir.dimension_ge_four N
  rw [coefficientCount_eq]
  apply Nat.mul_pos hh
  have hs : 16 ≤ HistoryAdjointCasimir.dimension N ^ 2 := by nlinarith
  omega

def gapMass (N : ℕ) : ℝ := Real.sqrt (HistoryHaarJointHessian.gapSq N)

theorem gapMass_pos (N : ℕ) : 0 < gapMass N :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (HistoryHaarJointHessian.gapSq_lower N))

theorem gapMass_sq (N : ℕ) : gapMass N ^ 2 = HistoryHaarJointHessian.gapSq N :=
  Real.sq_sqrt (le_of_lt (lt_of_lt_of_le (by norm_num)
    (HistoryHaarJointHessian.gapSq_lower N)))

theorem gapMass_unique (N : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (he : m ^ 2 = HistoryHaarJointHessian.gapSq N) : m = gapMass N := by
  have hg := gapMass_sq N
  have hp := (gapMass_pos N).le
  nlinarith

theorem gapSq_bounds (N : ℕ) :
    (15 / 8 : ℝ) ≤ HistoryHaarJointHessian.gapSq N ∧
      HistoryHaarJointHessian.gapSq N ≤ 4 :=
  ⟨HistoryHaarJointHessian.gapSq_lower N, min_le_left _ _⟩

theorem gapMass_bounds (N : ℕ) : 1 < gapMass N ∧ gapMass N ≤ 2 := by
  have hs := gapMass_sq N
  have hp := gapMass_pos N
  have hb := gapSq_bounds N
  constructor <;> nlinarith

theorem consume_gap_interval (N : ℕ) (lo hi : ℝ) (hlo : 0 ≤ lo)
    (hloSq : lo ^ 2 ≤ HistoryHaarJointHessian.gapSq N)
    (hhi : 0 ≤ hi) (hhiSq : HistoryHaarJointHessian.gapSq N ≤ hi ^ 2) :
    lo ≤ gapMass N ∧ gapMass N ≤ hi := by
  have hs := gapMass_sq N
  have hp := gapMass_pos N
  constructor <;> nlinarith

structure Conclusions : Prop where
  actual_coefficient_count : ∀ N, coefficientCount N =
    Fintype.card (HistoryGaugeJets.CoordinateIndex N) *
      (HistoryAdjointCasimir.dimension N ^ 2 - 1)
  positive_count : ∀ N, 0 < coefficientCount N
  exact_mass_square : ∀ N, gapMass N ^ 2 = HistoryHaarJointHessian.gapSq N
  positive_mass : ∀ N, 0 < gapMass N
  unique_positive_mass : ∀ N m, 0 ≤ m → m ^ 2 = HistoryHaarJointHessian.gapSq N →
    m = gapMass N
  exact_uniform_bounds : ∀ N, 1 < gapMass N ∧ gapMass N ≤ 2

theorem generated : Conclusions where
  actual_coefficient_count := coefficientCount_eq
  positive_count := coefficientCount_pos
  exact_mass_square := gapMass_sq
  positive_mass := gapMass_pos
  unique_positive_mass := gapMass_unique
  exact_uniform_bounds := gapMass_bounds

end GeneratedFoundations.Arithmetic.HistoryResponseCertificates
