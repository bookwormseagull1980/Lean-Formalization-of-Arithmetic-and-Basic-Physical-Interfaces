module

public import GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow
public import GeneratedFoundations.Arithmetic.HistoryScalarGauge
public import GeneratedFoundations.Operations.SourceSpinCornerGroup

/-!
# Stabilizer of the full invariant history sector

The relative phase character has its actual rank-derived weights `(-n,1)`.
The right source action combines this character with the original two
source coordinates. Fixing all invariant upper histories determines its
special-unitary component uniquely. The conclusion concerns the entire
history subspace and retains the detail action on the original carrier.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate

namespace GeneratedFoundations.Arithmetic.HistoryPhaseStabilizer

open Operations.SourceSpinCorner (Mat2)
open Operations.SourceSpinCornerGroup
open HistoryJointCharge (Fibre)
open HistoryJointQuadraticResponse (RightSpace)

abbrev rightScalarMatrix := HistoryScalarGauge.rightScalarMatrix
abbrev stabilizerFrame := HistoryScalarGauge.stabilizerFrame

theorem stabilizer_response (n : ℕ) (z : Circle) :
    rightScalarMatrix n (stabilizerFrame n z) z =
      Matrix.diagonal ![1, ((z : ℂ) ^ (n + n))⁻¹] := by
  change ((z : ℂ) ^ n)⁻¹ • (HistoryScalarGauge.stabilizerFrame n z : Mat2) = _
  rw [HistoryScalarGauge.stabilizerFrame_matrix]
  have hz := pow_ne_zero n (Circle.coe_ne_zero z)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hz, pow_add, mul_inv_rev]

abbrev FixesSource := HistoryScalarGauge.FixesVacuum

theorem fixesSource_iff (n : ℕ) (g : SU2) (z : Circle) :
    FixesSource n g z ↔ g = stabilizerFrame n z := HistoryScalarGauge.fixesVacuum_iff n g z

def relativeAction (n : ℕ) (z : Circle) : Module.End ℂ (Fibre n) :=
  HistoryRelativePhase.block n (((z : ℂ) ^ n)⁻¹, (z : ℂ))

def rightAction (n : ℕ) (g : SU2) (z : Circle) : Module.End ℂ (RightSpace n) where
  toFun x := WithLp.toLp 2 fun i => ∑ j : Fin 2,
    (g : Mat2) i j • relativeAction n z (x j)
  map_add' x y := by
    apply PiLp.ext
    intro i
    simp [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply PiLp.ext
    intro i
    simp [map_smul, smul_smul, mul_comm]

def upper (n : ℕ) (f : HistoryPhaseProjection.HistorySpace n) : RightSpace n :=
  PiLp.single 2 0 (HistoryPhaseProjection.lift n f)

theorem relativeAction_lift (n : ℕ) (z : Circle)
    (f : HistoryPhaseProjection.HistorySpace n) :
    relativeAction n z (HistoryPhaseProjection.lift n f) =
      ((z : ℂ) ^ n)⁻¹ • HistoryPhaseProjection.lift n f := by
  have hp : HistoryPhaseProjection.projection n (HistoryPhaseProjection.lift n f) =
      HistoryPhaseProjection.lift n f := by
    change HistoryPhaseProjection.lift n
      ((HistoryPhaseProjection.average n).comp (HistoryPhaseProjection.lift n) f) = _
    rw [HistoryPhaseProjection.average_lift]
    rfl
  simp [relativeAction, HistoryRelativePhase.block_apply,
    HistoryPhaseProjection.residual, hp]

theorem rightAction_upper (n : ℕ) (g : SU2) (z : Circle)
    (f : HistoryPhaseProjection.HistorySpace n) (i : Fin 2) :
    rightAction n g z (upper n f) i =
      rightScalarMatrix n g z i 0 • HistoryPhaseProjection.lift n f := by
  change (∑ j : Fin 2, (g : Mat2) i j • relativeAction n z (upper n f j)) = _
  simp [upper, Fin.sum_univ_two, relativeAction_lift, HistoryScalarGauge.rightScalarMatrix,
    smul_smul, mul_comm]

/-- The stabilizer test is on all histories and the actual phase lift. -/
theorem fixes_all_upper_iff (n : ℕ) (g : SU2) (z : Circle) :
    (∀ f, rightAction n g z (upper n f) = upper n f) ↔ g = stabilizerFrame n z := by
  rw [← fixesSource_iff]
  constructor
  · intro h
    have hv := h (fun _ => 1)
    have h0 := congrArg (fun x : RightSpace n =>
      x 0 (HistoryModuleRepresentation.base n)) hv
    have h1 := congrArg (fun x : RightSpace n =>
      x 1 (HistoryModuleRepresentation.base n)) hv
    rw [rightAction_upper] at h0 h1
    change rightScalarMatrix n g z 0 0 * (1 : ℂ) = 1 at h0
    change rightScalarMatrix n g z 1 0 * (1 : ℂ) = 0 at h1
    simp only [mul_one] at h0 h1
    change (rightScalarMatrix n g z).mulVec ![1, 0] = ![1, 0]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · intro h f
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    apply PiLp.ext
    intro i
    rw [rightAction_upper]
    fin_cases i <;> simp [upper, h0, h1]

structure Conclusions : Prop where
  unique_stabilizer : ∀ n g z, FixesSource n g z ↔ g = stabilizerFrame n z
  entire_history_sector : ∀ n g z,
    (∀ f, rightAction n g z (upper n f) = upper n f) ↔ g = stabilizerFrame n z
  retained_lower_character : ∀ n z,
    rightScalarMatrix n (stabilizerFrame n z) z =
      Matrix.diagonal ![1, ((z : ℂ) ^ (n + n))⁻¹]

theorem generated : Conclusions where
  unique_stabilizer := fixesSource_iff
  entire_history_sector := fixes_all_upper_iff
  retained_lower_character := stabilizer_response

end GeneratedFoundations.Arithmetic.HistoryPhaseStabilizer
