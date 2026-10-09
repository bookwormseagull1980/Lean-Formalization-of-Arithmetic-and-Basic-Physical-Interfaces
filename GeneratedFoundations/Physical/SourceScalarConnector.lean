module

public import GeneratedFoundations.Physical.SourcePreExchangeResponse
public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Physical.SourceReversalRealConnector
public import GeneratedFoundations.Physical.SourcePhaseLift

/-!
# The elementary scalar connector in the source spin frame

The reversal is transported through the Gaussian-normalized spin coordinates.
Its commutation equation is solved for an arbitrary endomorphism of the actual
source spin carrier.  The unique second-column coordinate is a complex doublet;
equivalently the solution is a unique generated quaternion amplitude.

Independent pre-exchange source responses, rather than a diagonal group action,
force every natural connector to have this same reduced spin map.  The residual
right frame gives its second column phase weight three.  Colour changes cancel
on the actual tensor product.

These are the elementary P6 conditions on a single connector space.  They do not
exclude a model with several copies.  The split chiral realization below uses
the same reduced source map; no identification of the pre-exchange colour
carrier with the exchange-resolved sum is asserted here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Quaternion ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2 canonical specialUnitary_entries)
open GeneratedFoundations.Physical.ReversalRealConnector
open GeneratedFoundations.Physical.SourceJointResponse (S)

namespace GeneratedFoundations.Physical.SourceScalarConnector

/-- The source spin coordinates retain the Gaussian vacuum phase convention. -/
def spinCoordinates : S ≃ₗ[ℂ] Spinor :=
  SourceSpinIdentification.coordinateUnitary.symm.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℂ Spinor)

def sourceMatrix (h : Module.End ℂ S) : Mat2 :=
  SourceSpinIdentification.spinActionEquiv.symm h

theorem sourceMatrix_injective : Function.Injective sourceMatrix :=
  SourceSpinIdentification.spinActionEquiv.symm.injective

@[simp] theorem sourceMatrix_spinAction (M : Mat2) :
    sourceMatrix (SourceSpinIdentification.spinAction M) = M :=
  SourceSpinIdentification.spinActionEquiv.symm_apply_apply M

@[simp] theorem spinAction_sourceMatrix (h : Module.End ℂ S) :
    SourceSpinIdentification.spinAction (sourceMatrix h) = h :=
  SourceSpinIdentification.spinActionEquiv.apply_symm_apply h

theorem spinCoordinates_spinAction (M : Mat2) (s : S) :
    spinCoordinates (SourceSpinIdentification.spinAction M s) =
      M.mulVec (spinCoordinates s) := by
  obtain ⟨v, rfl⟩ := SourceSpinIdentification.coordinateUnitary.surjective s
  change WithLp.ofLp (SourceSpinIdentification.coordinateUnitary.symm
    (SourceSpinIdentification.spinAction M (SourceSpinIdentification.coordinateUnitary v))) =
    M.mulVec (WithLp.ofLp (SourceSpinIdentification.coordinateUnitary.symm
      (SourceSpinIdentification.coordinateUnitary v)))
  rw [SourceSpinIdentification.spinAction_coordinates]
  simp only [LinearIsometryEquiv.symm_apply_apply, WithLp.ofLp_toLp]

theorem spinCoordinates_apply (h : Module.End ℂ S) (s : S) :
    spinCoordinates (h s) = (sourceMatrix h).mulVec (spinCoordinates s) := by
  simpa only [spinAction_sourceMatrix] using
    spinCoordinates_spinAction (sourceMatrix h) s

/-- The specified source pseudoreal structure; its coordinates are not chosen anew. -/
def transportedReversal (s : S) : S := spinCoordinates.symm (reversal (spinCoordinates s))

@[simp] theorem spinCoordinates_reversal (s : S) :
    spinCoordinates (transportedReversal s) = reversal (spinCoordinates s) :=
  spinCoordinates.apply_symm_apply _

theorem transportedReversal_square (s : S) :
    transportedReversal (transportedReversal s) = -s := by
  simp [transportedReversal, reversal_square]

theorem transportedReversal_add (s t : S) :
    transportedReversal (s + t) = transportedReversal s + transportedReversal t := by
  simp [transportedReversal, reversal_add]

theorem transportedReversal_smul (a : ℂ) (s : S) :
    transportedReversal (a • s) = star a • transportedReversal s := by
  simp [transportedReversal, reversal_smul]

def ReversalCompatible (h : Module.End ℂ S) : Prop :=
  ∀ s, h (transportedReversal s) = transportedReversal (h s)

/-- The input endomorphism is unrestricted before imposing the reversal equation. -/
theorem reversalCompatible_iff_matrix (h : Module.End ℂ S) :
    ReversalCompatible h ↔ ReversalReal (sourceMatrix h) := by
  constructor
  · intro hh v
    have hv := congrArg spinCoordinates (hh (spinCoordinates.symm v))
    simpa only [spinCoordinates_apply, spinCoordinates_reversal,
      LinearEquiv.apply_symm_apply] using hv
  · intro hh s
    apply spinCoordinates.injective
    simpa only [spinCoordinates_apply, spinCoordinates_reversal] using hh (spinCoordinates s)

def doubletLift (H : Spinor) : Module.End ℂ S :=
  SourceSpinIdentification.spinAction (connectorOfDoublet H)

def doublet (h : Module.End ℂ S) : Spinor := doubletOfMatrix (sourceMatrix h)

@[simp] theorem sourceMatrix_doubletLift (H : Spinor) :
    sourceMatrix (doubletLift H) = connectorOfDoublet H :=
  sourceMatrix_spinAction _

@[simp] theorem doublet_doubletLift (H : Spinor) : doublet (doubletLift H) = H := by
  simp [doublet]

theorem doubletLift_injective : Function.Injective doubletLift := by
  intro H K h
  simpa only [doublet_doubletLift] using congrArg doublet h

theorem doubletLift_reversalCompatible (H : Spinor) : ReversalCompatible (doubletLift H) := by
  rw [reversalCompatible_iff_matrix, sourceMatrix_doubletLift]
  exact connectorOfDoublet_reversalReal H

theorem reversalCompatible_iff_unique_doublet (h : Module.End ℂ S) :
    ReversalCompatible h ↔ ∃! H : Spinor, h = doubletLift H := by
  rw [reversalCompatible_iff_matrix]
  constructor
  · intro hh
    obtain ⟨H, hH, huniq⟩ := (reversalReal_iff_existsUnique_doublet _).mp hh
    refine ⟨H, sourceMatrix_injective (hH.trans (sourceMatrix_doubletLift H).symm), ?_⟩
    intro K hK
    apply huniq
    rw [hK, sourceMatrix_doubletLift]
  · rintro ⟨H, rfl, _⟩
    rw [sourceMatrix_doubletLift]
    exact connectorOfDoublet_reversalReal H

@[simp] theorem sourceMatrix_quaternionSpin (q : ℍ) :
    sourceMatrix (SourceChiralCarrier.quaternionSpin q) =
      Geometry.SourceQuaternionAmplitude.matrixMap q := by
  rw [SourceChiralCarrier.quaternionSpin_eq_sourceAction, sourceMatrix_spinAction]

theorem reversalCompatible_iff_unique_quaternion (h : Module.End ℂ S) :
    ReversalCompatible h ↔ ∃! q : ℍ, h = SourceChiralCarrier.quaternionSpin q := by
  rw [reversalCompatible_iff_matrix]
  constructor
  · intro hh
    obtain ⟨q, hq, huniq⟩ :=
      (SourceReversalRealConnector.reversalReal_iff_unique_sourceAmplitude _).mp hh
    refine ⟨q, sourceMatrix_injective (hq.symm.trans (sourceMatrix_quaternionSpin q).symm), ?_⟩
    intro p hp
    apply huniq
    rw [hp, sourceMatrix_quaternionSpin]
  · rintro ⟨q, rfl, _⟩
    rw [sourceMatrix_quaternionSpin]
    exact SourceReversalRealConnector.matrixMap_reversalReal q

/-- Naturality first determines the reduced map; reality is tested on that map.
No tensor factorization is a hypothesis on the arbitrary input connector. -/
def Elementary (T : Module.End ℂ SourcePreExchangeResponse.FullCarrier) : Prop :=
  SourcePreExchangeResponse.SourceNatural T ∧
    ∀ h : Module.End ℂ S, T = SourcePreExchangeResponse.spinLift h → ReversalCompatible h

theorem elementary_iff_unique_doublet
    (T : Module.End ℂ SourcePreExchangeResponse.FullCarrier) :
    Elementary T ↔ ∃! H : Spinor,
      T = SourcePreExchangeResponse.spinLift (doubletLift H) := by
  constructor
  · rintro ⟨hT, hr⟩
    obtain ⟨h, hh, _⟩ :=
      (SourcePreExchangeResponse.sourceNatural_iff_existsUnique_spinor T).mp hT
    obtain ⟨H, hH, huniq⟩ := (reversalCompatible_iff_unique_doublet h).mp (hr h hh)
    refine ⟨H, hh.trans (congrArg SourcePreExchangeResponse.spinLift hH), ?_⟩
    intro K hK
    apply huniq
    exact SourcePreExchangeResponse.spinLift_injective (hh.symm.trans hK)
  · rintro ⟨H, hH, _⟩
    constructor
    · rw [hH, SourcePreExchangeResponse.sourceNatural_iff_natural]
      exact SourcePreExchangeResponse.spinLift_natural _
    · intro h hh
      have he : h = doubletLift H :=
        SourcePreExchangeResponse.spinLift_injective (hh.symm.trans hH)
      rw [he]
      exact doubletLift_reversalCompatible H

/-- The generated family satisfies naturality and reversal reality; these
properties need not be supplied as assumptions on its construction. -/
theorem canonical_elementary (H : Spinor) :
    Elementary (SourcePreExchangeResponse.spinLift (doubletLift H)) := by
  apply (elementary_iff_unique_doublet _).mpr
  refine ⟨H, rfl, ?_⟩
  intro K hK
  exact doubletLift_injective
    (SourcePreExchangeResponse.spinLift_injective hK.symm)

theorem specialUnitary_reversalReal (U : SU2) : ReversalReal (U : Mat2) := by
  rw [specialUnitary_entries U U.property]
  change ReversalReal (canonicalMatrix _ _)
  exact canonicalMatrix_reversalReal _ _

theorem sourceOperator_reversalCompatible (U : SU2) :
    ReversalCompatible (SourceJointResponse.sourceOperator 1 U) := by
  rw [← SourceSpinIdentification.spinAction_sourceOperator,
    reversalCompatible_iff_matrix, sourceMatrix_spinAction]
  exact specialUnitary_reversalReal U

theorem stabilizerFrame_inverse_matrix (z : Circle) :
    ((SourcePhaseLift.stabilizerFrame z)⁻¹ : SU2) =
      SourcePhaseLift.stabilizerFrame z⁻¹ := by
  apply Subtype.ext
  change (SourcePhaseLift.stabilizerFrame z : Mat2).conjTranspose =
    (SourcePhaseLift.stabilizerFrame z⁻¹ : Mat2)
  rw [SourcePhaseLift.stabilizerFrame_matrix, SourcePhaseLift.stabilizerFrame_matrix]
  have hc : conj (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv] using (Circle.coe_inv_eq_conj z).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hc]

def gaugeMatrix (gL : SU2) (z : Circle) (M : Mat2) : Mat2 :=
  (gL : Mat2) * M * (((SourcePhaseLift.stabilizerFrame z)⁻¹ : SU2) : Mat2)

theorem gaugeMatrix_reversalReal (gL : SU2) (z : Circle) {M : Mat2}
    (hM : ReversalReal M) : ReversalReal (gaugeMatrix gL z M) :=
  SourceReversalRealConnector.reversalReal_mul
    (SourceReversalRealConnector.reversalReal_mul (specialUnitary_reversalReal gL) hM)
    (specialUnitary_reversalReal (SourcePhaseLift.stabilizerFrame z)⁻¹)

/-- The weight is derived from the inverse right frame, without a charge-table premise. -/
theorem gaugeMatrix_secondColumn (gL : SU2) (z : Circle) (M : Mat2) :
    doubletOfMatrix (gaugeMatrix gL z M) =
      (z : ℂ) ^ 3 • (gL : Mat2).mulVec (doubletOfMatrix M) := by
  rw [gaugeMatrix, stabilizerFrame_inverse_matrix, SourcePhaseLift.stabilizerFrame_matrix]
  ext i
  simp [doubletOfMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]
  ring

theorem gaugeMatrix_doubletLift (gL : SU2) (z : Circle) (H : Spinor) :
    gaugeMatrix gL z (connectorOfDoublet H) =
      connectorOfDoublet ((z : ℂ) ^ 3 • (gL : Mat2).mulVec H) := by
  calc
    _ = connectorOfDoublet (doubletOfMatrix
        (gaugeMatrix gL z (connectorOfDoublet H))) :=
      (connectorOfDoublet_doubletOfMatrix _
        (gaugeMatrix_reversalReal gL z (connectorOfDoublet_reversalReal H))).symm
    _ = _ := by rw [gaugeMatrix_secondColumn, doubletOfMatrix_connectorOfDoublet]

def gaugeSpin (gL : SU2) (z : Circle) (h : Module.End ℂ S) : Module.End ℂ S :=
  SourceSpinIdentification.spinAction (gL : Mat2) * h *
    SourceSpinIdentification.spinAction (((SourcePhaseLift.stabilizerFrame z)⁻¹ : SU2) : Mat2)

theorem sourceMatrix_gaugeSpin (gL : SU2) (z : Circle) (h : Module.End ℂ S) :
    sourceMatrix (gaugeSpin gL z h) = gaugeMatrix gL z (sourceMatrix h) := by
  simp [sourceMatrix, gaugeSpin, gaugeMatrix]

theorem gaugeSpin_reversalCompatible (gL : SU2) (z : Circle) {h : Module.End ℂ S}
    (hh : ReversalCompatible h) : ReversalCompatible (gaugeSpin gL z h) := by
  rw [reversalCompatible_iff_matrix, sourceMatrix_gaugeSpin]
  exact gaugeMatrix_reversalReal gL z ((reversalCompatible_iff_matrix h).mp hh)

theorem gaugeSpin_doubletLift (gL : SU2) (z : Circle) (H : Spinor) :
    gaugeSpin gL z (doubletLift H) =
      doubletLift ((z : ℂ) ^ 3 • (gL : Mat2).mulVec H) := by
  apply sourceMatrix_injective
  rw [sourceMatrix_gaugeSpin, sourceMatrix_doubletLift, sourceMatrix_doubletLift,
    gaugeMatrix_doubletLift]

theorem gaugeSpin_doublet (gL : SU2) (z : Circle) (h : Module.End ℂ S) :
    doublet (gaugeSpin gL z h) = (z : ℂ) ^ 3 • (gL : Mat2).mulVec (doublet h) := by
  simpa only [doublet, sourceMatrix_gaugeSpin] using
    gaugeMatrix_secondColumn gL z (sourceMatrix h)

/-- The same invertible colour response in source and target cancels on the actual carrier. -/
theorem colour_response_cancels (g : SourcePreExchangeResponse.C ≃ₗ[ℂ]
    SourcePreExchangeResponse.C) (gL : SU2) (z : Circle) (h : Module.End ℂ S) :
    TensorProduct.map g.toLinearMap (SourceSpinIdentification.spinAction (gL : Mat2)) *
        SourcePreExchangeResponse.spinLift h *
        TensorProduct.map g.symm.toLinearMap (SourceSpinIdentification.spinAction
          (((SourcePhaseLift.stabilizerFrame z)⁻¹ : SU2) : Mat2)) =
      SourcePreExchangeResponse.spinLift (gaugeSpin gL z h) := by
  have hg : g.toLinearMap * g.symm.toLinearMap = 1 := by
    apply LinearMap.ext
    intro c
    exact g.apply_symm_apply c
  unfold SourcePreExchangeResponse.spinLift gaugeSpin
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, mul_one, hg]

/-- The full split chiral connector uses precisely this reduced source spin map. -/
def scalarConnector (H : Spinor) : Module.End ℂ SourceChiralCarrier.FullMatter :=
  SourceChiralCarrier.connector (doubletLift H)

theorem scalarConnector_isSelfAdjoint (H : Spinor) : IsSelfAdjoint (scalarConnector H) :=
  SourceChiralCarrier.connector_isSelfAdjoint _

theorem scalarConnector_odd (H : Spinor) :
    SourceChiralCarrier.grading * scalarConnector H +
      scalarConnector H * SourceChiralCarrier.grading = 0 :=
  SourceChiralCarrier.connector_odd _

theorem doubletLift_eq_quaternionSpin (H : Spinor) :
    doubletLift H = SourceChiralCarrier.quaternionSpin
      (Geometry.SourceQuaternionAmplitude.ofMatrix (connectorOfDoublet H)) := by
  apply sourceMatrix_injective
  rw [sourceMatrix_doubletLift, sourceMatrix_quaternionSpin]
  exact (SourceReversalRealConnector.matrixMap_ofMatrix_of_reversalReal _
    (connectorOfDoublet_reversalReal H)).symm

theorem scalarConnector_hermite {b : ℝ} (hb : 0 < b) (H : Spinor)
    (x : SourceChiralCarrier.FullMatter) :
    SourceChiralCarrier.hermiteIsometry hb (scalarConnector H x) =
      SourceCliffordConnector.sourceConnector hb 4
        (Geometry.SourceQuaternionAmplitude.ofMatrix (connectorOfDoublet H))
        (SourceChiralCarrier.hermiteIsometry hb x) := by
  unfold scalarConnector
  rw [doubletLift_eq_quaternionSpin]
  exact SourceChiralCarrier.hermiteIsometry_connector hb _ x

end GeneratedFoundations.Physical.SourceScalarConnector
