module

public import GeneratedFoundations.Operations.SourceWeylPreparation
public import GeneratedFoundations.Operations.PreparedTraceDifferentiation

/-!
# Prepared response on the Gaussian Hermite corner

The source trace identifies the prepared logarithmic response with the
normalized matrix trace response. Its Hessian is the source trace covariance.
On the Hermitian corner its kernel consists of real multiples of the corner
projection, and its traceless restriction is positive definite.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Operator
open GeneratedFoundations.Operations.SourceSpinCorner (End)

namespace GeneratedFoundations.Operations.SourcePreparedResponse

open FiniteWeylAverage (Index Mat)
open SourceWeylPreparation (corner projection sourceTrace modes modes_injective)
open PreparedTraceForm (Hermitian Traceless)

local instance positiveDimension (n : ℕ) : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩

variable {b : ℝ} (hb : 0 < b) (n : ℕ)

def sourceResponse (K : Mat n) : ℝ :=
  Real.log ((sourceTrace hb n (corner hb n (NormedSpace.exp K))).re /
    ((n + 1 : ℕ) : ℝ))

theorem sourceResponse_eq :
    sourceResponse hb n = PreparedTraceDifferentiation.response (Index n) := by
  funext K
  simp only [sourceResponse, SourceWeylPreparation.sourceTrace_corner,
    PreparedTraceDifferentiation.response_apply, Index, ZMod.card]

theorem sourceResponse_hasFDerivAt_zero :
    HasFDerivAt (sourceResponse hb n)
      (PreparedTraceDifferentiation.normalizedTrace (Index n)) 0 := by
  rw [sourceResponse_eq]
  exact PreparedTraceDifferentiation.response_hasFDerivAt_zero (Index n)

theorem sourceResponse_fderiv_hasFDerivAt_zero :
    HasFDerivAt (fderiv ℝ (sourceResponse hb n))
      (PreparedTraceDifferentiation.responseHessian (Index n)) 0 := by
  rw [sourceResponse_eq]
  exact PreparedTraceDifferentiation.response_fderiv_hasFDerivAt_zero (Index n)

theorem sourceResponse_hessian (K L : Mat n) :
    fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 K L =
      PreparedTraceForm.preparedForm (Index n) K L := by
  rw [sourceResponse_eq]
  exact PreparedTraceDifferentiation.response_hessian_apply (Index n) K L

def sourceCovariance (T S : End) : ℝ :=
  (sourceTrace hb n (T * S)).re / ((n + 1 : ℕ) : ℝ) -
    (sourceTrace hb n T).re * (sourceTrace hb n S).re /
      (((n + 1 : ℕ) : ℝ) ^ 2)

theorem sourceCovariance_corner (K L : Mat n) :
    sourceCovariance hb n (corner hb n K) (corner hb n L) =
      PreparedTraceForm.preparedForm (Index n) K L := by
  have hmul : corner hb n K * corner hb n L = corner hb n (K * L) :=
    (FiniteHermiteCorner.corner_mul hb (modes n) (modes_injective n) K L).symm
  simp only [sourceCovariance, hmul, SourceWeylPreparation.sourceTrace_corner,
    PreparedTraceForm.preparedForm_apply, Index, ZMod.card]

theorem sourceResponse_hessian_source (K L : Mat n) :
    fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 K L =
      sourceCovariance hb n (corner hb n K) (corner hb n L) := by
  rw [sourceResponse_hessian, sourceCovariance_corner]

/-- The Hermitian directions embedded in the Gaussian operator space. -/
def hermitianMap : Hermitian (Index n) →ₗ[ℝ] End :=
  ((corner hb n).restrictScalars ℝ).comp
    (PreparedTraceForm.hermitianSubspace (Index n)).subtype

@[simp] theorem hermitianMap_apply (K : Hermitian (Index n)) :
    hermitianMap hb n K = corner hb n (K : Mat n) := rfl

theorem hermitianMap_injective : Function.Injective (hermitianMap hb n) := by
  intro K L h
  apply Subtype.ext
  exact FiniteHermiteCorner.corner_injective hb (modes n) (modes_injective n) h

theorem hermitianMap_adjoint (K : Hermitian (Index n)) :
    (hermitianMap hb n K).adjoint = hermitianMap hb n K := by
  change (FiniteHermiteCorner.corner hb (modes n) (K : Mat n)).adjoint = _
  rw [FiniteHermiteCorner.corner_adjoint,
    (PreparedTraceForm.hermitian_isHermitian (Index n) K).eq]
  rfl

def hermitianSpace : Submodule ℝ End := LinearMap.range (hermitianMap hb n)

theorem mem_hermitianSpace_iff (T : End) :
    T ∈ hermitianSpace hb n ↔
      T.adjoint = T ∧ projection hb n * T * projection hb n = T := by
  constructor
  · rintro ⟨K, rfl⟩
    refine ⟨hermitianMap_adjoint hb n K, ?_⟩
    exact (FiniteHermiteCorner.mem_range_corner_iff hb (modes n)
      (modes_injective n) _).mp ⟨(K : Mat n), rfl⟩
  · rintro ⟨hself, hcompression⟩
    let X : Mat n := FiniteHermiteCorner.entries hb (modes n) T
    have hX : corner hb n X = T :=
      (FiniteHermiteCorner.corner_entries hb (modes n) T).trans hcompression
    have hherm : X.IsHermitian := by
      change X.conjTranspose = X
      apply FiniteHermiteCorner.corner_injective hb (modes n) (modes_injective n)
      calc
        corner hb n X.conjTranspose = (corner hb n X).adjoint :=
          (FiniteHermiteCorner.corner_adjoint hb (modes n) X).symm
        _ = corner hb n X := by rw [hX, hself]
    exact ⟨⟨X, hherm.isSelfAdjoint⟩, hX⟩

def tracelessMap : Traceless (Index n) →ₗ[ℝ] End :=
  (hermitianMap hb n).comp (PreparedTraceForm.tracelessSubspace (Index n)).subtype

@[simp] theorem tracelessMap_apply (K : Traceless (Index n)) :
    tracelessMap hb n K = corner hb n (K.val : Mat n) := rfl

theorem tracelessMap_injective : Function.Injective (tracelessMap hb n) :=
  (hermitianMap_injective hb n).comp Subtype.val_injective

def tracelessSpace : Submodule ℝ End := LinearMap.range (tracelessMap hb n)

theorem sourceTrace_traceless (K : Traceless (Index n)) :
    sourceTrace hb n (tracelessMap hb n K) = 0 := by
  rw [tracelessMap_apply, SourceWeylPreparation.sourceTrace_corner]
  exact (PreparedTraceForm.mem_tracelessSubspace (Index n) K.val).mp K.property

theorem mem_tracelessSpace_iff (T : End) :
    T ∈ tracelessSpace hb n ↔ T ∈ hermitianSpace hb n ∧ sourceTrace hb n T = 0 := by
  constructor
  · rintro ⟨K, rfl⟩
    exact ⟨⟨K.val, rfl⟩, sourceTrace_traceless hb n K⟩
  · rintro ⟨hherm, htrace⟩
    obtain ⟨K, rfl⟩ := hherm
    have ht : Matrix.trace (K : Mat n) = 0 := by
      simpa only [hermitianMap_apply, SourceWeylPreparation.sourceTrace_corner] using htrace
    exact ⟨⟨K, (PreparedTraceForm.mem_tracelessSubspace (Index n) K).mpr ht⟩, rfl⟩

theorem finrank_hermitianSpace :
    Module.finrank ℝ (hermitianSpace hb n) = (n + 1) ^ 2 := by
  change Module.finrank ℝ (LinearMap.range (hermitianMap hb n)) = _
  rw [LinearMap.finrank_range_of_inj (hermitianMap_injective hb n),
    PreparedTraceForm.finrank_hermitian]
  simp only [Index, ZMod.card]

theorem finrank_tracelessSpace :
    Module.finrank ℝ (tracelessSpace hb n) = (n + 1) ^ 2 - 1 := by
  change Module.finrank ℝ (LinearMap.range (tracelessMap hb n)) = _
  rw [LinearMap.finrank_range_of_inj (tracelessMap_injective hb n),
    PreparedTraceForm.finrank_traceless]
  simp only [Index, ZMod.card]

theorem sourceResponse_hessian_nonneg (K : Hermitian (Index n)) :
    0 ≤ fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 (K : Mat n) (K : Mat n) := by
  rw [sourceResponse_hessian]
  exact PreparedTraceForm.preparedForm_nonneg (Index n)
    (PreparedTraceForm.hermitian_isHermitian (Index n) K)

theorem corner_scalar_iff (K : Mat n) (a : ℝ) :
    corner hb n K = a • projection hb n ↔ K = a • (1 : Mat n) := by
  have hs : corner hb n (a • (1 : Mat n)) = a • projection hb n :=
    (corner hb n).map_smul_of_tower a 1
  rw [← hs]
  exact (FiniteHermiteCorner.corner_injective hb (modes n) (modes_injective n)).eq_iff

theorem sourceResponse_hessian_self_eq_zero_iff (K : Hermitian (Index n)) :
    fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 (K : Mat n) (K : Mat n) = 0 ↔
      ∃ a : ℝ, hermitianMap hb n K = a • projection hb n := by
  rw [sourceResponse_hessian,
    PreparedTraceForm.preparedForm_self_eq_zero_iff (Index n)
      (PreparedTraceForm.hermitian_isHermitian (Index n) K)]
  simp only [hermitianMap_apply, corner_scalar_iff]

theorem sourceResponse_hessian_kernel_iff (K : Hermitian (Index n)) :
    (∀ L : Hermitian (Index n),
      fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 (K : Mat n) (L : Mat n) = 0) ↔
      ∃ a : ℝ, hermitianMap hb n K = a • projection hb n := by
  simp only [sourceResponse_hessian, PreparedTraceForm.preparedForm_kernel_iff,
    hermitianMap_apply, corner_scalar_iff]

theorem sourceResponse_hessian_traceless_pos (K : Traceless (Index n)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 (K.val : Mat n) (K.val : Mat n) := by
  rw [sourceResponse_hessian]
  exact PreparedTraceForm.preparedForm_traceless_pos (Index n) K hK

theorem sourceCovariance_nonneg {T : End} (hT : T ∈ hermitianSpace hb n) :
    0 ≤ sourceCovariance hb n T T := by
  obtain ⟨K, rfl⟩ := hT
  rw [hermitianMap_apply, sourceCovariance_corner]
  exact PreparedTraceForm.preparedForm_nonneg (Index n)
    (PreparedTraceForm.hermitian_isHermitian (Index n) K)

theorem sourceCovariance_self_eq_zero_iff {T : End} (hT : T ∈ hermitianSpace hb n) :
    sourceCovariance hb n T T = 0 ↔ ∃ a : ℝ, T = a • projection hb n := by
  obtain ⟨K, rfl⟩ := hT
  rw [hermitianMap_apply, sourceCovariance_corner,
    PreparedTraceForm.preparedForm_self_eq_zero_iff (Index n)
      (PreparedTraceForm.hermitian_isHermitian (Index n) K)]
  simp only [corner_scalar_iff]

theorem sourceCovariance_traceless_pos {T : End}
    (hT : T ∈ tracelessSpace hb n) (hT0 : T ≠ 0) :
    0 < sourceCovariance hb n T T := by
  obtain ⟨K, rfl⟩ := hT
  rw [tracelessMap_apply, sourceCovariance_corner]
  apply PreparedTraceForm.preparedForm_traceless_pos (Index n) K
  intro h
  apply hT0
  rw [h, map_zero]

theorem sourceResponse_hessian_unitary_conj
    (U : Matrix.unitaryGroup (Index n) ℂ) (K L : Mat n) :
    fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0
      ((U : Mat n) * K * (U : Mat n).conjTranspose)
      ((U : Mat n) * L * (U : Mat n).conjTranspose) =
        fderiv ℝ (fderiv ℝ (sourceResponse hb n)) 0 K L := by
  rw [sourceResponse_hessian, sourceResponse_hessian]
  exact PreparedTraceForm.preparedForm_unitary_conj (Index n) U K L

theorem sourceCovariance_weyl_conj (a d : Index n) (K L : Mat n) :
    sourceCovariance hb n
      (SourceWeylPreparation.sourceWeyl hb n a d * corner hb n K *
        (SourceWeylPreparation.sourceWeyl hb n a d).adjoint)
      (SourceWeylPreparation.sourceWeyl hb n a d * corner hb n L *
        (SourceWeylPreparation.sourceWeyl hb n a d).adjoint) =
      sourceCovariance hb n (corner hb n K) (corner hb n L) := by
  rw [SourceWeylPreparation.sourceWeyl_conjugation,
    SourceWeylPreparation.sourceWeyl_conjugation,
    sourceCovariance_corner, sourceCovariance_corner]
  exact PreparedTraceForm.preparedForm_unitary_conj (Index n)
    ⟨FiniteWeylAverage.weyl n a d, FiniteWeylAverage.weyl_unitary n a d⟩ K L

end GeneratedFoundations.Operations.SourcePreparedResponse
