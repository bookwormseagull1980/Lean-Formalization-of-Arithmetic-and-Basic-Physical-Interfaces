module

public import GeneratedFoundations.Geometry.SourcePreExchangeResponse
public import GeneratedFoundations.Geometry.SourceSpinIdentification
public import GeneratedFoundations.Operations.SourceReversalRealConnector

/-!
# Reversal-real responses in the generated Gaussian--Haar frame

All endomorphisms of the actual degree-one Haar carrier are retained before
solving the reversal equation. The Gaussian vacuum convention fixes the
coordinates; a reversal-compatible response has a unique complex-doublet
coordinate. Neither a matter multiplicity nor a physical phase weight enters
this common-source classification.
-/

@[expose] public section

noncomputable section

open scoped Quaternion ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2 canonical specialUnitary_entries)
open GeneratedFoundations.Operations.ReversalRealConnector
open GeneratedFoundations.Geometry.SourceJointResponse (S)

namespace GeneratedFoundations.Geometry.SourceScalarResponse

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

theorem specialUnitary_reversalReal (U : SU2) : ReversalReal (U : Mat2) := by
  rw [specialUnitary_entries U U.property]
  change ReversalReal (canonicalMatrix _ _)
  exact canonicalMatrix_reversalReal _ _

theorem sourceOperator_reversalCompatible (U : SU2) :
    ReversalCompatible (SourceSymmetricUnitary.sourceOperator 1 U) := by
  rw [← SourceSpinIdentification.spinAction_sourceOperator,
    reversalCompatible_iff_matrix, sourceMatrix_spinAction]
  exact specialUnitary_reversalReal U

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

/-- Both frames belong to the same generated source group. A frame is a
comparison coordinate, not an additional source input. -/
abbrev Frame := SU2 × SU2

def frameMatrix (g : Frame) (M : Mat2) : Mat2 :=
  (g.1 : Mat2) * M * (g.2 : Mat2).conjTranspose

theorem specialUnitary_adjoint_reversalReal (U : SU2) :
    ReversalReal (U : Mat2).conjTranspose :=
  Operations.SourceReversalRealConnector.reversalReal_adjoint (specialUnitary_reversalReal U)

theorem frameMatrix_reversalReal (g : Frame) {M : Mat2} (hM : ReversalReal M) :
    ReversalReal (frameMatrix g M) :=
  Operations.SourceReversalRealConnector.reversalReal_mul
    (Operations.SourceReversalRealConnector.reversalReal_mul
      (specialUnitary_reversalReal g.1) hM)
    (specialUnitary_adjoint_reversalReal g.2)

@[simp] theorem frameMatrix_one (M : Mat2) : frameMatrix 1 M = M := by
  simp [frameMatrix]

theorem frameMatrix_mul (g k : Frame) (M : Mat2) :
    frameMatrix (g * k) M = frameMatrix g (frameMatrix k M) := by
  simp [frameMatrix, Matrix.conjTranspose_mul, mul_assoc]

def frameDoublet (g : Frame) (v : Spinor) : Spinor :=
  doubletOfMatrix (frameMatrix g (connectorOfDoublet v))

theorem connectorOfDoublet_frameDoublet (g : Frame) (v : Spinor) :
    connectorOfDoublet (frameDoublet g v) = frameMatrix g (connectorOfDoublet v) :=
  connectorOfDoublet_doubletOfMatrix _
    (frameMatrix_reversalReal g (connectorOfDoublet_reversalReal v))

@[simp] theorem frameDoublet_one (v : Spinor) : frameDoublet 1 v = v := by
  simp [frameDoublet]

theorem frameDoublet_mul (g k : Frame) (v : Spinor) :
    frameDoublet (g * k) v = frameDoublet g (frameDoublet k v) := by
  apply connectorOfDoublet_injective
  rw [connectorOfDoublet_frameDoublet, connectorOfDoublet_frameDoublet,
    connectorOfDoublet_frameDoublet, frameMatrix_mul]

theorem frameDoublet_inverse (g : Frame) (v : Spinor) :
    frameDoublet g⁻¹ (frameDoublet g v) = v := by
  rw [← frameDoublet_mul, inv_mul_cancel, frameDoublet_one]

def frameSpin (g : Frame) (h : Module.End ℂ S) : Module.End ℂ S :=
  SourceSpinIdentification.spinAction (g.1 : Mat2) * h *
    SourceSpinIdentification.spinAction (g.2 : Mat2).conjTranspose

theorem sourceMatrix_frameSpin (g : Frame) (h : Module.End ℂ S) :
    sourceMatrix (frameSpin g h) = frameMatrix g (sourceMatrix h) := by
  simp [sourceMatrix, frameSpin, frameMatrix]

theorem frameSpin_doubletLift (g : Frame) (v : Spinor) :
    frameSpin g (doubletLift v) = doubletLift (frameDoublet g v) := by
  apply sourceMatrix_injective
  rw [sourceMatrix_frameSpin, sourceMatrix_doubletLift, sourceMatrix_doubletLift,
    connectorOfDoublet_frameDoublet]

end GeneratedFoundations.Geometry.SourceScalarResponse
