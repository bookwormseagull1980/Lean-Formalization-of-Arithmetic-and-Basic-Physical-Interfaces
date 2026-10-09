module

public import GeneratedFoundations.Physical.SourceMatterCharge
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity and the right source response

The full response and its right restriction act on the Hilbert carriers
already constructed from the source. Their diagonal forms establish
self-adjointness and positivity. Restriction to the right carrier retains
the same neutral vacuum, giving a seven-dimensional charged quotient.

The colour coefficient is a specified nonnegative response parameter.
No identification with a normalized Lie-algebra Casimir is assumed here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder

namespace GeneratedFoundations.Physical.SourceChargedResponse

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceChargeLattice SourceMatterCharge

section Eigenbasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℂ E] in
private theorem matrix_of_eigenbasis (b : OrthonormalBasis ι ℂ E)
    (A : Module.End ℂ E) (w : ι → ℂ)
    (hA : ∀ i, A (b i) = w i • b i) :
    LinearMap.toMatrix b.toBasis b.toBasis A = Matrix.diagonal w := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.toBasis.repr (A (b j)) i = _
  rw [hA, map_smul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, hij]

omit [FiniteDimensional ℂ E] in
private theorem symmetric_of_real_eigenbasis (b : OrthonormalBasis ι ℂ E)
    (A : Module.End ℂ E) (w : ι → ℝ)
    (hA : ∀ i, A (b i) = (w i : ℂ) • b i) : A.IsSymmetric := by
  apply (LinearMap.isHermitian_toMatrix_iff b).mp
  rw [matrix_of_eigenbasis b A _ hA, Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

omit [FiniteDimensional ℂ E] in
private theorem positive_of_real_eigenbasis (b : OrthonormalBasis ι ℂ E)
    (A : Module.End ℂ E) (w : ι → ℝ)
    (hA : ∀ i, A (b i) = (w i : ℂ) • b i)
    (hw : ∀ i, 0 ≤ w i) : A.IsPositive := by
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  rw [matrix_of_eigenbasis b A _ hA, Matrix.posSemidef_diagonal_iff]
  intro i
  exact (RCLike.ofReal_nonneg (K := ℂ)).2 (hw i)

end Eigenbasis

private theorem kernel_intertwining_iff
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (A : Module.End ℂ E) (B : Module.End ℂ F) (f : E →ₗ[ℂ] F)
    (hf : Function.Injective f) (h : ∀ x, B (f x) = f (A x)) (x : E) :
    A x = 0 ↔ B (f x) = 0 := by
  constructor
  · intro hx
    exact (h x).trans ((congrArg f hx).trans (map_zero f))
  · intro hx
    exact hf (((h x).symm.trans hx).trans (map_zero f).symm)

theorem hyperchargeOperator_isSelfAdjoint : IsSelfAdjoint hyperchargeOperator := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
  apply symmetric_of_real_eigenbasis fullBasis hyperchargeOperator
    (fun i => (generatedCharge (sectorOf i) : ℝ) / 6)
  intro i
  simpa using hyperchargeOperator_basis i

theorem chargedResponse_isSelfAdjoint (κ : ℝ) : IsSelfAdjoint (chargedResponse κ) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
    (symmetric_of_real_eigenbasis fullBasis _ (responseWeight κ) (chargedResponse_basis κ))

theorem chargedResponse_isPositive {κ : ℝ} (hκ : 0 ≤ κ) :
    (chargedResponse κ).IsPositive :=
  positive_of_real_eigenbasis fullBasis _ (responseWeight κ)
    (chargedResponse_basis κ) (responseWeight_nonneg hκ)

/-- The right generator retains both spin columns of the actual source carrier. -/
def rightCharge : Module.End ℂ SourceCarrier :=
  (3 : ℂ) • spinOnSource twiceSpin + primitiveRelativeSource

def rightHypercharge : Module.End ℂ SourceCarrier := (1 / 6 : ℂ) • rightCharge

def rightColourResponse (κ : ℝ) : Module.End ℂ SourceCarrier :=
  (κ : ℂ) • relativeSource 1 0

def rightResponse (κ : ℝ) : Module.End ℂ SourceCarrier :=
  rightColourResponse κ + rightHypercharge * rightHypercharge

def rightIndex (i : SourceIndex) : FullIndex := (i.1, Sum.inr i.2)

theorem fullBasis_rightIndex (i : SourceIndex) :
    fullBasis (rightIndex i) = rightInclusion (sourceBasis i) := by
  rcases i with ⟨c, s⟩
  exact fullBasis_right c s

theorem rightInclusion_injective : Function.Injective rightInclusion := by
  intro x y h
  exact congrArg (fun z : FullMatter => (WithLp.ofLp z).2) h

theorem generatedCharge_right (x : SourceCarrier) :
    generatedChargeOperator (rightInclusion x) = rightInclusion (rightCharge x) := by
  simp [generatedChargeOperator, chargeOperator, twiceRightGenerator, relativeGenerator,
    diagonalBlocks_right, rightCharge, map_add, map_smul]

theorem hypercharge_right (x : SourceCarrier) :
    hyperchargeOperator (rightInclusion x) = rightInclusion (rightHypercharge x) := by
  simp [hyperchargeOperator, rightHypercharge, generatedCharge_right, map_smul]

theorem colourResponse_right (κ : ℝ) (x : SourceCarrier) :
    colourCasimir κ (rightInclusion x) = rightInclusion (rightColourResponse κ x) := by
  change (κ : ℂ) • diagonalBlocks (relativeSource 1 0) (relativeSource 1 0)
    (rightInclusion x) = rightInclusion ((κ : ℂ) • relativeSource 1 0 x)
  exact (congrArg (fun y : FullMatter => (κ : ℂ) • y)
    (diagonalBlocks_right (relativeSource 1 0) (relativeSource 1 0) x)).trans
      (map_smul rightInclusion (κ : ℂ) (relativeSource 1 0 x)).symm

theorem chargedResponse_right (κ : ℝ) (x : SourceCarrier) :
    chargedResponse κ (rightInclusion x) = rightInclusion (rightResponse κ x) := by
  simp [chargedResponse, rightResponse, colourResponse_right, hypercharge_right,
    Module.End.mul_apply, map_add]

theorem rightResponse_basis (κ : ℝ) (i : SourceIndex) :
    rightResponse κ (sourceBasis i) =
      (responseWeight κ (rightIndex i) : ℂ) • sourceBasis i := by
  apply rightInclusion_injective
  rw [← chargedResponse_right, ← fullBasis_rightIndex, chargedResponse_basis, map_smul]
  rw [fullBasis_rightIndex]

theorem rightResponse_isSelfAdjoint (κ : ℝ) : IsSelfAdjoint (rightResponse κ) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp
    (symmetric_of_real_eigenbasis sourceBasis _
      (fun i => responseWeight κ (rightIndex i)) (rightResponse_basis κ))

theorem rightResponse_isPositive {κ : ℝ} (hκ : 0 ≤ κ) :
    (rightResponse κ).IsPositive :=
  positive_of_real_eigenbasis sourceBasis _
    (fun i => responseWeight κ (rightIndex i)) (rightResponse_basis κ)
    (fun i => responseWeight_nonneg hκ (rightIndex i))

def rightNeutralVector : SourceCarrier := sourceBasis (Sum.inr 0, 0)

def rightNeutralLine : Submodule ℂ SourceCarrier := ℂ ∙ rightNeutralVector

theorem rightNeutralVector_ne_zero : rightNeutralVector ≠ 0 :=
  sourceBasis.toBasis.ne_zero (Sum.inr 0, 0)

theorem rightInclusion_neutral : rightInclusion rightNeutralVector = neutralVector := by
  exact (fullBasis_right (Sum.inr 0) 0).symm

theorem rightInclusion_mem_neutral_iff (x : SourceCarrier) :
    rightInclusion x ∈ neutralLine ↔ x ∈ rightNeutralLine := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, rightInclusion_injective ?_⟩
    simpa [map_smul, rightInclusion_neutral] using hc
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c, by rw [map_smul, rightInclusion_neutral]⟩

theorem rightCharge_kernel : LinearMap.ker rightCharge = rightNeutralLine := by
  apply Submodule.ext
  intro x
  calc
    x ∈ LinearMap.ker rightCharge ↔ rightCharge x = 0 := Iff.rfl
    _ ↔ generatedChargeOperator (rightInclusion x) = 0 :=
      kernel_intertwining_iff rightCharge generatedChargeOperator rightInclusion
        rightInclusion_injective generatedCharge_right x
    _ ↔ rightInclusion x ∈ LinearMap.ker generatedChargeOperator := Iff.rfl
    _ ↔ rightInclusion x ∈ neutralLine :=
      Iff.of_eq (congrArg (fun K : Submodule ℂ FullMatter => rightInclusion x ∈ K)
        generatedChargeOperator_kernel)
    _ ↔ x ∈ rightNeutralLine := rightInclusion_mem_neutral_iff x

theorem rightResponse_kernel {κ : ℝ} (hκ : 0 ≤ κ) :
    LinearMap.ker (rightResponse κ) = rightNeutralLine := by
  apply Submodule.ext
  intro x
  calc
    x ∈ LinearMap.ker (rightResponse κ) ↔ rightResponse κ x = 0 := Iff.rfl
    _ ↔ chargedResponse κ (rightInclusion x) = 0 :=
      kernel_intertwining_iff (rightResponse κ) (chargedResponse κ) rightInclusion
        rightInclusion_injective (chargedResponse_right κ) x
    _ ↔ rightInclusion x ∈ LinearMap.ker (chargedResponse κ) := Iff.rfl
    _ ↔ rightInclusion x ∈ neutralLine :=
      Iff.of_eq (congrArg (fun K : Submodule ℂ FullMatter => rightInclusion x ∈ K)
        (chargedResponse_kernel hκ))
    _ ↔ x ∈ rightNeutralLine := rightInclusion_mem_neutral_iff x

theorem rightNeutralLine_finrank : Module.finrank ℂ rightNeutralLine = 1 :=
  finrank_span_singleton rightNeutralVector_ne_zero

theorem rightChargedQuotient_finrank :
    Module.finrank ℂ (SourceCarrier ⧸ rightNeutralLine) = 7 := by
  have h := rightNeutralLine.finrank_quotient_add_finrank
  rw [rightNeutralLine_finrank, sourceCarrier_finrank] at h
  omega

theorem rightResponse_quotient_finrank {κ : ℝ} (hκ : 0 ≤ κ) :
    Module.finrank ℂ (SourceCarrier ⧸ LinearMap.ker (rightResponse κ)) = 7 := by
  rw [rightResponse_kernel hκ]
  exact rightChargedQuotient_finrank

end GeneratedFoundations.Physical.SourceChargedResponse
