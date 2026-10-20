module

public import GeneratedFoundations.Arithmetic.HistoryAdjointCasimir

/-!
# The complete real Lie directions of arithmetic operations

The carrier is the actual history--phase operation algebra. Subtracting its
calculated trace part and taking the skew part gives all skew-adjoint,
traceless directions. Surjectivity is proved by the fixed-point equation,
not assumed as a coefficient parametrization. The coefficients need not be
unique: the constructed projection has a precisely stated image.

Connection and derivative values in that image give the same nonlinear
curvature formula as the full operator jets. The trace and adjoint constraints
are preserved by the actual commutator and by generated unitary frames.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Arithmetic.HistoryLieAlgebra

open HistoryCliffordAction (Index Algebra Space action)
open HistoryAdjointCasimir (dimension)

def IsLie (N : ℕ) (X : Algebra N) : Prop :=
  X.conjTranspose = -X ∧ Matrix.trace X = 0

/-- All unitary coordinates of the complete generated operation algebra.
This group is larger than the two source-frame factors. -/
abbrev UnitaryFrame (N : ℕ) := Matrix.unitaryGroup (Index N) ℂ

abbrev SpecialFrame (N : ℕ) := Matrix.specialUnitaryGroup (Index N) ℂ

def unitaryConjugate (N : ℕ) (u : UnitaryFrame N) (X : Algebra N) : Algebra N :=
  (u : Algebra N) * X * (u : Algebra N).conjTranspose

theorem unitary_conjugate_mem (N : ℕ) (u : UnitaryFrame N) (X : Algebra N)
    (hX : IsLie N X) : IsLie N (unitaryConjugate N u X) := by
  have hu : (u : Algebra N).conjTranspose * (u : Algebra N) = 1 :=
    Matrix.UnitaryGroup.star_mul_self u
  constructor
  · rw [unitaryConjugate, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hX.1]
    noncomm_ring
  · rw [unitaryConjugate, Matrix.trace_mul_cycle, hu, one_mul, hX.2]

def centered (N : ℕ) (X : Algebra N) : Algebra N :=
  X - (Matrix.trace X / (dimension N : ℂ)) • 1

theorem trace_centered (N : ℕ) (X : Algebra N) : Matrix.trace (centered N X) = 0 := by
  have hd : (dimension N : ℂ) ≠ 0 := by
    exact_mod_cast (HistoryAdjointCasimir.dimension_pos N).ne'
  rw [centered, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  change Matrix.trace X - (Matrix.trace X / (dimension N : ℂ)) * (dimension N : ℂ) = 0
  simp [hd]

theorem centered_traceless (N : ℕ) (X : Algebra N) (hX : Matrix.trace X = 0) :
    centered N X = X := by simp [centered, hX]

def lieMatrix (N : ℕ) (X : Algebra N) : Algebra N :=
  (1 / 2 : ℂ) • (centered N X - (centered N X).conjTranspose)

theorem lieMatrix_adjoint (N : ℕ) (X : Algebra N) :
    (lieMatrix N X).conjTranspose = -lieMatrix N X := by
  simp only [lieMatrix, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  simp
  module

theorem lieMatrix_trace (N : ℕ) (X : Algebra N) : Matrix.trace (lieMatrix N X) = 0 := by
  rw [lieMatrix, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose,
    trace_centered]
  simp

theorem lieMatrix_mem (N : ℕ) (X : Algebra N) : IsLie N (lieMatrix N X) :=
  ⟨lieMatrix_adjoint N X, lieMatrix_trace N X⟩

theorem lieMatrix_fixed (N : ℕ) (X : Algebra N) (hX : IsLie N X) : lieMatrix N X = X := by
  rw [lieMatrix, centered_traceless N X hX.2, hX.1]
  module

theorem lieMatrix_surjective (N : ℕ) (X : Algebra N) (hX : IsLie N X) :
    ∃ c : Algebra N, lieMatrix N c = X := ⟨X, lieMatrix_fixed N X hX⟩

theorem lieMatrix_image (N : ℕ) (X : Algebra N) :
    (∃ c : Algebra N, lieMatrix N c = X) ↔ IsLie N X := by
  constructor
  · rintro ⟨c, rfl⟩
    exact lieMatrix_mem N c
  · exact lieMatrix_surjective N X

theorem lieMatrix_idempotent (N : ℕ) (X : Algebra N) :
    lieMatrix N (lieMatrix N X) = lieMatrix N X :=
  lieMatrix_fixed N _ (lieMatrix_mem N X)

theorem lieMatrix_add (N : ℕ) (X Y : Algebra N) :
    lieMatrix N (X + Y) = lieMatrix N X + lieMatrix N Y := by
  simp only [lieMatrix, centered, Matrix.trace_add, add_div, add_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
  module

theorem lieMatrix_real_smul (N : ℕ) (t : ℝ) (X : Algebra N) :
    lieMatrix N ((t : ℂ) • X) = (t : ℂ) • lieMatrix N X := by
  have hc : centered N ((t : ℂ) • X) = (t : ℂ) • centered N X := by
    rw [centered, Matrix.trace_smul, centered, smul_sub, smul_smul]
    congr 1
    ring_nf
  rw [lieMatrix, hc, Matrix.conjTranspose_smul]
  have ht : star (t : ℂ) = (t : ℂ) := by simp
  rw [ht]
  unfold lieMatrix
  module

theorem sub_mem (N : ℕ) {X Y : Algebra N} (hX : IsLie N X) (hY : IsLie N Y) :
    IsLie N (X - Y) := by
  constructor
  · rw [Matrix.conjTranspose_sub, hX.1, hY.1]
    abel
  · rw [Matrix.trace_sub, hX.2, hY.2, sub_self]

theorem add_mem (N : ℕ) {X Y : Algebra N} (hX : IsLie N X) (hY : IsLie N Y) :
    IsLie N (X + Y) := by
  constructor
  · rw [Matrix.conjTranspose_add, hX.1, hY.1, neg_add]
  · rw [Matrix.trace_add, hX.2, hY.2, add_zero]

theorem commutator_mem (N : ℕ) {X Y : Algebra N} (hX : IsLie N X) (hY : IsLie N Y) :
    IsLie N (X * Y - Y * X) := by
  constructor
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX.1, hY.1]
    noncomm_ring
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]

theorem conjugate_mem (N : ℕ) (g : HistoryElementaryConnector.Frame) (X : Algebra N)
    (hX : IsLie N X) : IsLie N (HistoryEffectiveFrames.conjugate N g X) := by
  constructor
  · rw [HistoryEffectiveFrames.conjugate_adjoint, hX.1]
    simp [HistoryEffectiveFrames.conjugate, mul_neg, neg_mul]
  · rw [HistoryEffectiveFrames.conjugate, Matrix.trace_mul_cycle,
      HistoryElementaryConnector.frame_adjoint_mul, one_mul, hX.2]

structure ConnectionJet (N : ℕ) where
  value : HistoryGaugeJets.CoordinateIndex N → Algebra N
  derivative : HistoryGaugeJets.CoordinateIndex N → HistoryGaugeJets.CoordinateIndex N → Algebra N

def connectionMatrix (N : ℕ) (A : ConnectionJet N) (μ : HistoryGaugeJets.CoordinateIndex N) :
    Algebra N := lieMatrix N (A.value μ)

def derivativeMatrix (N : ℕ) (A : ConnectionJet N)
    (μ ν : HistoryGaugeJets.CoordinateIndex N) : Algebra N := lieMatrix N (A.derivative μ ν)

def curvature (N : ℕ) (A : ConnectionJet N) (μ ν : HistoryGaugeJets.CoordinateIndex N) :
    Algebra N := derivativeMatrix N A μ ν - derivativeMatrix N A ν μ +
      (connectionMatrix N A μ * connectionMatrix N A ν -
        connectionMatrix N A ν * connectionMatrix N A μ)

theorem curvature_mem (N : ℕ) (A : ConnectionJet N) (μ ν : HistoryGaugeJets.CoordinateIndex N) :
    IsLie N (curvature N A μ ν) :=
  add_mem N (sub_mem N (lieMatrix_mem N _) (lieMatrix_mem N _))
    (commutator_mem N (lieMatrix_mem N _) (lieMatrix_mem N _))

def operatorJet (N : ℕ) (A : ConnectionJet N) : HistoryGaugeJets.ConnectionJet N where
  value μ := action N (connectionMatrix N A μ)
  derivative μ ν := action N (derivativeMatrix N A μ ν)

theorem curvature_operatorJet (N : ℕ) (A : ConnectionJet N)
    (μ ν : HistoryGaugeJets.CoordinateIndex N) :
    HistoryGaugeJets.curvature (operatorJet N A) μ ν = action N (curvature N A μ ν) := by
  simp only [HistoryGaugeJets.curvature, Geometry.ConnectionJetAlgebra.curvature,
    operatorJet, curvature, map_add, map_sub, map_mul]

theorem action_isLie (N : ℕ) (X : Algebra N) (hX : IsLie N X) :
    (action N X).adjoint = -action N X ∧ LinearMap.trace ℂ (Space N) (action N X) = 0 := by
  constructor
  · rw [HistoryCliffordAction.action_adjoint, hX.1, map_neg]
  · rw [HistoryAdjointCasimir.trace_action, hX.2]

structure Conclusions : Prop where
  complete_image : ∀ N X, (∃ c : Algebra N, lieMatrix N c = X) ↔ IsLie N X
  exact_projection : ∀ N X, lieMatrix N (lieMatrix N X) = lieMatrix N X
  closed_commutator : ∀ N (X Y : Algebra N), IsLie N X → IsLie N Y →
    IsLie N (X * Y - Y * X)
  frame_invariant : ∀ N g X, IsLie N X → IsLie N (HistoryEffectiveFrames.conjugate N g X)
  all_unitary_frames : ∀ N (u : UnitaryFrame N) X,
    IsLie N X → IsLie N (unitaryConjugate N u X)
  full_curvature : ∀ N A μ ν,
    HistoryGaugeJets.curvature (operatorJet N A) μ ν = action N (curvature N A μ ν)
  constrained_curvature : ∀ N A μ ν, IsLie N (curvature N A μ ν)

theorem generated : Conclusions where
  complete_image := lieMatrix_image
  exact_projection := lieMatrix_idempotent
  closed_commutator := fun N _ _ => commutator_mem N
  frame_invariant := conjugate_mem
  all_unitary_frames := unitary_conjugate_mem
  full_curvature := curvature_operatorJet
  constrained_curvature := curvature_mem

end GeneratedFoundations.Arithmetic.HistoryLieAlgebra
