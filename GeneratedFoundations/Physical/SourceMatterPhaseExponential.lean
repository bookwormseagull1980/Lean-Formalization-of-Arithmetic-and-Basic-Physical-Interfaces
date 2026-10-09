module

public import GeneratedFoundations.Physical.SourceGaugeTransport
public import GeneratedFoundations.Physical.SourceMatterCharge
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The exponential of the actual source hypercharge

The residual circle action is diagonalized in the specified orthonormal
source basis, including every colour, spin and chiral label. Its generator
is the hypercharge operator already constructed from the relative source
generator and the right-spin generator. The matrix exponential is then
transported to continuous operators on the actual matter Hilbert space.

On the right retained line, this flow is the original Gaussian number
flow in the fixed vacuum/first-excitation spin frame. The complete matter
flow nevertheless has the previously established twelve-pi period.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Kronecker Matrix.Norms.Operator

namespace GeneratedFoundations.Physical.SourceMatterPhaseExponential

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceMatterCharge SourceChargeLattice SourceGaugeTransport

/-- The residual action evaluated in all six retained coordinate blocks. -/
theorem coordinate_phase_apply (z : Circle) (x : GlobalGaugeKernel.Matter) :
    GlobalGaugeKernel.representation (1, 1, z) x =
      (((z : ℂ) • x.1.1, ((z : ℂ) ^ 3)⁻¹ • x.1.2),
        (((z : ℂ) ^ 4 • x.2.1.1, ((z : ℂ) ^ 2)⁻¹ • x.2.1.2),
          (x.2.2.1, ((z : ℂ) ^ 6)⁻¹ • x.2.2.2))) := by
  change
    ((((z : ℂ) • ((1 : GlobalGaugeKernel.Mat3) ⊗ₖ
          (1 : Operations.SourceSpinCorner.Mat2))).mulVec x.1.1,
        (((z : ℂ) ^ 3)⁻¹ • (1 : Operations.SourceSpinCorner.Mat2)).mulVec x.1.2),
      ((((z : ℂ) ^ 4) • (1 : GlobalGaugeKernel.Mat3)).mulVec x.2.1.1,
        (((z : ℂ) ^ 2)⁻¹ • (1 : GlobalGaugeKernel.Mat3)).mulVec x.2.1.2),
        ((1 : GlobalGaugeKernel.Mat1).mulVec x.2.2.1,
          (((z : ℂ) ^ 6)⁻¹ • (1 : GlobalGaugeKernel.Mat1)).mulVec x.2.2.2)) = _
  simp only [Matrix.one_kronecker_one, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem coordinate_phase_pack (z : Circle) (f : FullIndex → ℂ) :
    GlobalGaugeKernel.representation (1, 1, z) (pack f) =
      pack (fun i => (z : ℂ) ^ generatedCharge (sectorOf i) * f i) := by
  rw [coordinate_phase_apply]
  apply Prod.ext
  · apply Prod.ext <;> funext i <;>
      norm_num [pack, sectorOf, colourSector, spinSector, generatedCharge,
        chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]
  · apply Prod.ext
    · apply Prod.ext <;> funext i <;>
        norm_num [pack, sectorOf, colourSector, spinSector, generatedCharge,
          chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]
    · apply Prod.ext <;> funext i <;>
        norm_num [pack, sectorOf, colourSector, spinSector, generatedCharge,
          chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]

/-- Every one of the sixteen actual basis vectors has its source charge character. -/
theorem phaseAction_basis (z : Circle) (i : FullIndex) :
    phaseAction z (fullBasis i) =
      (z : ℂ) ^ generatedCharge (sectorOf i) • fullBasis i := by
  apply coordinates.injective
  change coordinates (representation (1, 1, z) (fullBasis i)) = _
  rw [coordinates_intertwines, coordinates_basis, map_smul, coordinates_basis,
    coordinate_phase_pack, ← pack.map_smul]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem phase_character (t : ℝ) (q : ℤ) :
    (SourcePhaseLift.phase t : ℂ) ^ q =
      Complex.exp (((t : ℂ) * Complex.I) * ((q : ℂ) / 6)) := by
  rw [SourcePhaseLift.phase, Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem phaseFlow_basis (t : ℝ) (i : FullIndex) :
    phaseFlow t (fullBasis i) =
      Complex.exp (((t : ℂ) * Complex.I) *
        ((generatedCharge (sectorOf i) : ℂ) / 6)) • fullBasis i := by
  rw [phaseFlow, phaseAction_basis, phase_character]

/-- The permutation is the one already used for the sixteen-state Hermite corner. -/
def hermiteHypercharge (i : SourceCliffordConnector.ColourIndex 4) : ℂ :=
  (generatedCharge (sectorOf (colourChiralEquiv.symm i)) : ℂ) / 6

private theorem fullMatrixCoordinates_diagonal (A : Module.End ℂ FullMatter)
    (w : FullIndex → ℂ) (hw : ∀ i, A (fullBasis i) = w i • fullBasis i) :
    fullMatrixCoordinates A = Matrix.diagonal (fun i => w (colourChiralEquiv.symm i)) := by
  have hv (j : SourceCliffordConnector.ColourIndex 4) :
      A (hermiteBasis j) = w (colourChiralEquiv.symm j) • hermiteBasis j := by
    simpa only [hermiteBasis, OrthonormalBasis.reindex_apply] using
      hw (colourChiralEquiv.symm j)
  ext i j
  simp only [fullMatrixCoordinates, LinearMap.toMatrixOrthonormal_apply_apply, hv,
    inner_smul_right, OrthonormalBasis.inner_eq_ite]
  by_cases hij : i = j <;> simp [hij]

theorem hypercharge_matrix :
    fullMatrixCoordinates hyperchargeOperator = Matrix.diagonal hermiteHypercharge :=
  fullMatrixCoordinates_diagonal hyperchargeOperator
    (fun i => (generatedCharge (sectorOf i) : ℂ) / 6) hyperchargeOperator_basis

theorem phaseFlow_matrix (t : ℝ) :
    fullMatrixCoordinates (phaseFlow t) =
      Matrix.diagonal (fun i => Complex.exp (((t : ℂ) * Complex.I) * hermiteHypercharge i)) :=
  fullMatrixCoordinates_diagonal (phaseFlow t)
    (fun i => Complex.exp (((t : ℂ) * Complex.I) *
      ((generatedCharge (sectorOf i) : ℂ) / 6))) (phaseFlow_basis t)

private theorem exp_smul_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (w : ι → ℂ) :
    NormedSpace.exp (z • Matrix.diagonal w) =
      Matrix.diagonal (fun i => Complex.exp (z * w i)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j <;>
    simp [hij, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

theorem phaseFlow_matrix_eq_exp (t : ℝ) :
    fullMatrixCoordinates (phaseFlow t) =
      NormedSpace.exp (((t : ℂ) * Complex.I) •
        fullMatrixCoordinates hyperchargeOperator) := by
  exact (phaseFlow_matrix t).trans
    ((exp_smul_diagonal ((t : ℂ) * Complex.I) hermiteHypercharge).symm.trans
      (congrArg NormedSpace.exp
        (congrArg (fun M : SourceCliffordConnector.ColourMatrix 4 =>
          ((t : ℂ) * Complex.I) • M) hypercharge_matrix.symm)))

/-- Continuous endomorphisms carry the operator norm of the original Hilbert space. -/
abbrev MatterEnd := FullMatter →L[ℂ] FullMatter

local instance : NormedRing MatterEnd := ContinuousLinearMap.toNormedRing

local instance : NormedAlgebra ℂ MatterEnd := ContinuousLinearMap.toNormedAlgebra

local instance : IsTopologicalRing MatterEnd :=
  NonUnitalSeminormedRing.toIsTopologicalRing

private theorem algebraEquiv_eq_one_iff {A B : Type*} [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) (a : A) : e a = 1 ↔ a = 1 := by
  constructor
  · intro h
    apply e.injective
    exact h.trans e.map_one.symm
  · intro h
    subst a
    exact e.map_one

def continuousModel : Module.End ℂ FullMatter ≃ₐ[ℂ] MatterEnd :=
  Module.End.toContinuousLinearMap FullMatter

@[simp] theorem continuousModel_apply (A : Module.End ℂ FullMatter) (x : FullMatter) :
    continuousModel A x = A x := rfl

/-- The matrix model uses the previously fixed source/Hermite basis permutation. -/
def matrixRealization : SourceCliffordConnector.ColourMatrix 4 ≃ₐ[ℂ] MatterEnd :=
  fullMatrixCoordinates.symm.toAlgEquiv.trans continuousModel

@[simp] theorem matrixRealization_coordinates (A : Module.End ℂ FullMatter) :
    matrixRealization (fullMatrixCoordinates A) = continuousModel A := by
  simp [matrixRealization]

private theorem matrixRealization_continuous : Continuous matrixRealization :=
  matrixRealization.toLinearMap.continuous_of_finiteDimensional

attribute [local irreducible] matrixRealization

private theorem continuous_algebraHom_map_exp {A B : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Ring B] [Algebra ℂ B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
    (f : A →ₐ[ℂ] B) (hf : Continuous f) (a : A) :
    f (NormedSpace.exp a) = NormedSpace.exp (f a) := by
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  refine ((NormedSpace.expSeries_summable' (𝕂 := ℂ) a).hasSum.map f hf).tsum_eq.symm.trans ?_
  apply tsum_congr
  intro n
  simp only [Function.comp_def, map_smul, map_pow]

private theorem matrixRealization_exp (M : SourceCliffordConnector.ColourMatrix 4) :
    matrixRealization (NormedSpace.exp M) = NormedSpace.exp (matrixRealization M) :=
  continuous_algebraHom_map_exp matrixRealization.toAlgHom matrixRealization_continuous M

/-- Actual operator exponential; no exponential or topology is postulated on raw linear maps. -/
theorem phaseFlow_eq_exp (t : ℝ) :
    continuousModel (phaseFlow t) =
      NormedSpace.exp (((t : ℂ) * Complex.I) • continuousModel hyperchargeOperator) := by
  calc
    continuousModel (phaseFlow t) = matrixRealization (fullMatrixCoordinates (phaseFlow t)) :=
      (matrixRealization_coordinates (phaseFlow t)).symm
    _ = matrixRealization (NormedSpace.exp
        (((t : ℂ) * Complex.I) • fullMatrixCoordinates hyperchargeOperator)) :=
      congrArg matrixRealization (phaseFlow_matrix_eq_exp t)
    _ = NormedSpace.exp (matrixRealization
        (((t : ℂ) * Complex.I) • fullMatrixCoordinates hyperchargeOperator)) :=
      matrixRealization_exp _
    _ = NormedSpace.exp (((t : ℂ) * Complex.I) • continuousModel hyperchargeOperator) :=
      congrArg NormedSpace.exp
        ((matrixRealization.toLinearMap.map_smul ((t : ℂ) * Complex.I)
          (fullMatrixCoordinates hyperchargeOperator)).trans
          (congrArg (fun A : MatterEnd => ((t : ℂ) * Complex.I) • A)
            (matrixRealization_coordinates hyperchargeOperator)))

theorem phaseFlow_apply_eq_exp (t : ℝ) (x : FullMatter) :
    phaseFlow t x =
      NormedSpace.exp (((t : ℂ) * Complex.I) • continuousModel hyperchargeOperator) x := by
  exact DFunLike.congr_fun (phaseFlow_eq_exp t) x

/-- The exponential in the actual normed model has the full matter period. -/
theorem exp_hypercharge_eq_one_iff (t : ℝ) :
    NormedSpace.exp (((t : ℂ) * Complex.I) • continuousModel hyperchargeOperator) = 1 ↔
      ∃ k : ℤ, t = k * (12 * Real.pi) := by
  calc
    _ ↔ continuousModel (phaseFlow t) = 1 :=
      Iff.of_eq (congrArg (fun A : MatterEnd => A = 1) (phaseFlow_eq_exp t).symm)
    _ ↔ phaseFlow t = 1 := algebraEquiv_eq_one_iff continuousModel (phaseFlow t)
    _ ↔ ∃ k : ℤ, t = k * (12 * Real.pi) := phaseFlow_eq_one_iff t

/-- The right retained scalar line tensored with the actual two-state spin carrier. -/
def rightScalarSpinInclusion : S →ₗ[ℂ] FullMatter :=
  rightInclusion.comp (sourceCarrierCoordinates.toLinearMap.comp
    ((LinearMap.inr ℂ Coloured Scalar).comp (TensorProduct.mk ℂ L S (lineBasis 0))))

theorem rightScalarSpinInclusion_apply (s : S) :
    rightScalarSpinInclusion s =
      rightInclusion (WithLp.toLp 2 (0, lineBasis 0 ⊗ₜ[ℂ] s)) := rfl

@[simp] theorem rightScalarSpinInclusion_basis (s : SpinLabel) :
    rightScalarSpinInclusion (spinBasis s) = fullBasis (Sum.inr 0, Sum.inr s) := by
  simp [rightScalarSpinInclusion_apply]

theorem phaseFlow_right_scalar_vacuum (t : ℝ) :
    phaseFlow t (fullBasis (Sum.inr 0, Sum.inr 0)) =
      fullBasis (Sum.inr 0, Sum.inr 0) := by
  rw [phaseFlow_basis]
  norm_num [sectorOf, colourSector, spinSector, generatedCharge, chargeWeight,
    twiceRightWeight, baseRelativeWeight, relativeWeight]

theorem phaseFlow_right_scalar_excitation (t : ℝ) :
    phaseFlow t (fullBasis (Sum.inr 0, Sum.inr 1)) =
      Complex.exp (-Complex.I * (t : ℂ)) • fullBasis (Sum.inr 0, Sum.inr 1) := by
  have hq : generatedCharge (sectorOf (Sum.inr 0, Sum.inr 1)) = -6 := by
    norm_num [sectorOf, colourSector, spinSector, generatedCharge, chargeWeight,
      twiceRightWeight, baseRelativeWeight, relativeWeight]
  have he : ((t : ℂ) * Complex.I) * (((-6 : ℤ) : ℂ) / 6) =
      -Complex.I * (t : ℂ) := by
    push_cast
    ring
  rw [phaseFlow_basis, hq, he]

private theorem intertwines_on_basis {E F ι : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (b : Module.Basis ι ℂ E) (A : Module.End ℂ F) (B : Module.End ℂ E)
    (f : E →ₗ[ℂ] F) (h : ∀ i, A (f (b i)) = f (B (b i))) (x : E) :
    A (f x) = f (B x) := by
  have he : A.comp f = f.comp B := by
    apply b.ext
    intro i
    exact h i
  exact LinearMap.congr_fun he x

private theorem intertwines_on_two_basis {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (b : Module.Basis (Fin 2) ℂ E) (A : Module.End ℂ F) (B : Module.End ℂ E)
    (f : E →ₗ[ℂ] F) (v₀ v₁ : F) (z : ℂ)
    (hf₀ : f (b 0) = v₀) (hf₁ : f (b 1) = v₁)
    (hA₀ : A v₀ = v₀) (hA₁ : A v₁ = z • v₁)
    (hB₀ : B (b 0) = b 0) (hB₁ : B (b 1) = z • b 1) (x : E) :
    A (f x) = f (B x) := by
  apply intertwines_on_basis b A B f _ x
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [hf₀, hA₀, hB₀, hf₀]
  · rw [hf₁, hA₁, hB₁, map_smul, hf₁]

/-- The entire right scalar two-state block, with the original Gaussian phase convention. -/
theorem phaseFlow_rightScalarSpin (t : ℝ) (s : S) :
    phaseFlow t (rightScalarSpinInclusion s) =
      rightScalarSpinInclusion (SourceSpinIdentification.spinAction
        (Operations.SourceNumberFlow.numberFlowMatrix t) s) := by
  exact intertwines_on_two_basis spinBasis.toBasis (phaseFlow t)
    (SourceSpinIdentification.spinAction (Operations.SourceNumberFlow.numberFlowMatrix t))
    rightScalarSpinInclusion (fullBasis (Sum.inr 0, Sum.inr 0))
    (fullBasis (Sum.inr 0, Sum.inr 1)) (Complex.exp (-Complex.I * (t : ℂ)))
    (rightScalarSpinInclusion_basis 0) (rightScalarSpinInclusion_basis 1)
    (phaseFlow_right_scalar_vacuum t) (phaseFlow_right_scalar_excitation t)
    (SourceSpinIdentification.spinAction_flow_vacuum t)
    (SourceSpinIdentification.spinAction_flow_excitation t) s

/-- Restriction of the full matter flow to the actual original Gaussian two-state carrier. -/
theorem phaseFlow_sourceNumber {b : ℝ} (hb : 0 < b) (t : ℝ)
    (v : SourceVacuumTransport.V hb) :
    phaseFlow t (rightScalarSpinInclusion (SourceSpinIdentification.sourceUnitary hb v)) =
      rightScalarSpinInclusion (SourceSpinIdentification.sourceUnitary hb
        (SourceVacuumTransport.sourceAction hb (Operations.SourceNumberFlow.numberFlowMatrix t) v)) := by
  rw [phaseFlow_rightScalarSpin, SourceSpinIdentification.sourceUnitary_matrix]

theorem sourceNumber_ambient {b : ℝ} (hb : 0 < b) (t : ℝ)
    (v : SourceVacuumTransport.V hb) :
    (SourceVacuumTransport.sourceAction hb (Operations.SourceNumberFlow.numberFlowMatrix t) v :
      Correlation.ComplexGaussianStates.ComplexL2) =
        Operations.SourceNumberFlow.numberFlow hb t v := by
  rw [SourceVacuumTransport.sourceAction_control,
    Operations.SourceNumberFlow.numberFlow_control]

end GeneratedFoundations.Physical.SourceMatterPhaseExponential
