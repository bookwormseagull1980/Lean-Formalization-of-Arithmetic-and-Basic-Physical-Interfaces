module

public import GeneratedFoundations.Arithmetic.HistoryElementaryConnector
public import GeneratedFoundations.Arithmetic.HistoryJointCharge
public import GeneratedFoundations.Geometry.SourcePhaseLift

/-!
# The scalar character forced by the actual arithmetic phase rank

The primitive joint charge fixes the invariant left weight to minus the
phase rank. Fixing the upper invariant source vector determines the entire
right special-unitary frame. Its inverse gives the doublet character of
weight equal to that rank. This is calculated on the same source spin
coordinate, then transported through the actual full arithmetic connector.

At rank three the frame is exactly the common original-source frame. Other
arithmetic ranks keep their own character; a physical weight is not inserted
in place of the generated arithmetic value.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace GeneratedFoundations.Arithmetic.HistoryScalarGauge

open Operations.SourceSpinCornerGroup (SU2 canonical specialUnitary_entries)
open Operations.ReversalRealConnector
open Geometry.SourceScalarResponse (Frame frameMatrix frameDoublet)

def stabilizerFrame (n : ℕ) (z : Circle) : SU2 :=
  ⟨canonical ((z : ℂ) ^ n) 0,
    Operations.SourceSpinCornerGroup.canonical_mem_specialUnitary _ _ (by simp [norm_pow])⟩

theorem stabilizerFrame_matrix (n : ℕ) (z : Circle) :
    (stabilizerFrame n z : Mat2) =
      Matrix.diagonal ![(z : ℂ) ^ n, ((z : ℂ) ^ n)⁻¹] := by
  have hc : conj (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv] using (Circle.coe_inv_eq_conj z).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stabilizerFrame, canonical, hc]

theorem stabilizerFrame_rank_three (z : Circle) :
    stabilizerFrame 3 z = Geometry.SourcePhaseLift.stabilizerFrame z := rfl

theorem stabilizerFrame_inverse (n : ℕ) (z : Circle) :
    (stabilizerFrame n z)⁻¹ = stabilizerFrame n z⁻¹ := by
  apply Subtype.ext
  change (stabilizerFrame n z : Mat2).conjTranspose = (stabilizerFrame n z⁻¹ : Mat2)
  rw [stabilizerFrame_matrix, stabilizerFrame_matrix]
  have hc : conj (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv] using (Circle.coe_inv_eq_conj z).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hc]

def rightScalarMatrix (n : ℕ) (g : SU2) (z : Circle) : Mat2 :=
  ((z : ℂ) ^ n)⁻¹ • (g : Mat2)

def FixesVacuum (n : ℕ) (g : SU2) (z : Circle) : Prop :=
  (rightScalarMatrix n g z).mulVec ![1, 0] = ![1, 0]

theorem fixesVacuum_iff (n : ℕ) (g : SU2) (z : Circle) :
    FixesVacuum n g z ↔ g = stabilizerFrame n z := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [rightScalarMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hz := pow_ne_zero n (Circle.coe_ne_zero z)
    have hg00 : (g : Mat2) 0 0 = (z : ℂ) ^ n :=
      ((inv_mul_eq_one₀ hz).mp h0).symm
    have hg10 : (g : Mat2) 1 0 = 0 := h1
    have he := specialUnitary_entries (g : Mat2) g.property
    have hc := congrArg (fun M : Mat2 => M 1 0) he
    have hg01 : (g : Mat2) 0 1 = 0 := by
      have hc' := congrArg conj hc
      simpa [canonical, hg10] using hc'.symm
    apply Subtype.ext
    change (g : Mat2) = canonical ((z : ℂ) ^ n) 0
    simpa only [hg00, hg01] using he
  · rintro rfl
    change (rightScalarMatrix n (stabilizerFrame n z) z).mulVec _ = _
    rw [rightScalarMatrix, stabilizerFrame_matrix]
    have hz := pow_ne_zero n (Circle.coe_ne_zero z)
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz]

def frame (n : ℕ) (g : SU2) (z : Circle) : Frame := (g, stabilizerFrame n z)

def gaugeMatrix (n : ℕ) (g : SU2) (z : Circle) (M : Mat2) : Mat2 :=
  frameMatrix (frame n g z) M

theorem gaugeMatrix_reversalReal (n : ℕ) (g : SU2) (z : Circle) {M : Mat2}
    (hM : ReversalReal M) : ReversalReal (gaugeMatrix n g z M) :=
  Geometry.SourceScalarResponse.frameMatrix_reversalReal _ hM

theorem gaugeMatrix_secondColumn (n : ℕ) (g : SU2) (z : Circle) (M : Mat2) :
    doubletOfMatrix (gaugeMatrix n g z M) =
      (z : ℂ) ^ n • (g : Mat2).mulVec (doubletOfMatrix M) := by
  unfold gaugeMatrix frameMatrix frame
  change doubletOfMatrix ((g : Mat2) * M *
    (stabilizerFrame n z : Mat2).conjTranspose) = _
  have hi : (stabilizerFrame n z : Mat2).conjTranspose =
      (stabilizerFrame n z⁻¹ : Mat2) := congrArg Subtype.val (stabilizerFrame_inverse n z)
  rw [hi, stabilizerFrame_matrix]
  ext i
  simp [doubletOfMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]
  ring

theorem gaugeMatrix_doubletLift (n : ℕ) (g : SU2) (z : Circle) (H : Spinor) :
    gaugeMatrix n g z (connectorOfDoublet H) =
      connectorOfDoublet ((z : ℂ) ^ n • (g : Mat2).mulVec H) := by
  calc
    _ = connectorOfDoublet (doubletOfMatrix
        (gaugeMatrix n g z (connectorOfDoublet H))) :=
      (connectorOfDoublet_doubletOfMatrix _
        (gaugeMatrix_reversalReal n g z (connectorOfDoublet_reversalReal H))).symm
    _ = _ := by rw [gaugeMatrix_secondColumn, doubletOfMatrix_connectorOfDoublet]

theorem frameDoublet_eq (n : ℕ) (g : SU2) (z : Circle) (H : Spinor) :
    frameDoublet (frame n g z) H = (z : ℂ) ^ n • (g : Mat2).mulVec H := by
  exact (gaugeMatrix_secondColumn n g z (connectorOfDoublet H)).trans
    (by rw [doubletOfMatrix_connectorOfDoublet])

/-- The same rank-dependent frame acts on the actual source operator;
the matrix and source descriptions retain all its entries. -/
def gaugeSpin (n : ℕ) (g : SU2) (z : Circle)
    (h : Module.End ℂ Geometry.SourceJointResponse.S) :=
  Geometry.SourceScalarResponse.frameSpin (frame n g z) h

theorem sourceMatrix_gaugeSpin (n : ℕ) (g : SU2) (z : Circle)
    (h : Module.End ℂ Geometry.SourceJointResponse.S) :
    Geometry.SourceScalarResponse.sourceMatrix (gaugeSpin n g z h) =
      gaugeMatrix n g z (Geometry.SourceScalarResponse.sourceMatrix h) :=
  Geometry.SourceScalarResponse.sourceMatrix_frameSpin (frame n g z) h

theorem gaugeSpin_reversalCompatible (n : ℕ) (g : SU2) (z : Circle)
    {h : Module.End ℂ Geometry.SourceJointResponse.S}
    (hh : Geometry.SourceScalarResponse.ReversalCompatible h) :
    Geometry.SourceScalarResponse.ReversalCompatible (gaugeSpin n g z h) := by
  rw [Geometry.SourceScalarResponse.reversalCompatible_iff_matrix,
    sourceMatrix_gaugeSpin]
  exact gaugeMatrix_reversalReal n g z
    ((Geometry.SourceScalarResponse.reversalCompatible_iff_matrix h).mp hh)

theorem gaugeSpin_doubletLift (n : ℕ) (g : SU2) (z : Circle) (H : Spinor) :
    gaugeSpin n g z (Geometry.SourceScalarResponse.doubletLift H) =
      Geometry.SourceScalarResponse.doubletLift ((z : ℂ) ^ n • (g : Mat2).mulVec H) := by
  rw [gaugeSpin, Geometry.SourceScalarResponse.frameSpin_doubletLift, frameDoublet_eq]

theorem gaugeSpin_doublet (n : ℕ) (g : SU2) (z : Circle)
    (h : Module.End ℂ Geometry.SourceJointResponse.S) :
    Geometry.SourceScalarResponse.doublet (gaugeSpin n g z h) =
      (z : ℂ) ^ n • (g : Mat2).mulVec (Geometry.SourceScalarResponse.doublet h) := by
  simp only [Geometry.SourceScalarResponse.doublet, sourceMatrix_gaugeSpin]
  exact gaugeMatrix_secondColumn n g z _

theorem actual_character (n : ℕ) :
    HistoryJointChargeLattice.generatedWeight n (false, Sum.inl 0) = -(n : ℤ) := by
  simp [HistoryJointChargeLattice.generatedWeight, HistoryJointChargeLattice.weight,
    HistoryJointChargeLattice.rightWeight, HistoryJointChargeLattice.relativeWeight]

theorem complete_connector_covariance (N n : ℕ) (g : SU2) (z : Circle) (H : Spinor) :
    HistoryElementaryConnector.frame N (frame n g z) *
        HistoryElementaryConnector.scalarConnector N H *
        (HistoryElementaryConnector.frame N (frame n g z)).conjTranspose =
      HistoryElementaryConnector.scalarConnector N ((z : ℂ) ^ n • (g : Mat2).mulVec H) := by
  rw [HistoryElementaryConnector.scalarConnector_covariant, frameDoublet_eq]

structure Conclusions : Prop where
  actual_weight : ∀ n,
    HistoryJointChargeLattice.generatedWeight n (false, Sum.inl 0) = -(n : ℤ)
  vacuum_stabilizer : ∀ n g z, FixesVacuum n g z ↔ g = stabilizerFrame n z
  full_source_character : ∀ n g z h,
    Geometry.SourceScalarResponse.doublet (gaugeSpin n g z h) =
      (z : ℂ) ^ n • (g : Mat2).mulVec (Geometry.SourceScalarResponse.doublet h)
  complete_covariance : ∀ N n g z H,
    HistoryElementaryConnector.frame N (frame n g z) *
        HistoryElementaryConnector.scalarConnector N H *
        (HistoryElementaryConnector.frame N (frame n g z)).conjTranspose =
      HistoryElementaryConnector.scalarConnector N ((z : ℂ) ^ n • (g : Mat2).mulVec H)

theorem generated : Conclusions where
  actual_weight := actual_character
  vacuum_stabilizer := fixesVacuum_iff
  full_source_character := gaugeSpin_doublet
  complete_covariance := complete_connector_covariance

end GeneratedFoundations.Arithmetic.HistoryScalarGauge
