module

public import GeneratedFoundations.Arithmetic.HistoryHaarJointEquation

/-!
# Exact reduction of the arithmetic joint differential response

The finite core is the span of the complete, already differentiated joint
Haar basis. Both inclusions below take their values in this core: the field
inclusion retains every finite differential field and the state inclusion
retains the full homogeneous history carrier. No independent diagonal form
is prescribed. The quadratic form and its polarization are evaluations of
the Hessian of the original nonlinear connection--state action.

The closure remains the original joint differential operator. Thus the
finite-core comparison includes both its field/state decomposition and the
unique full self-adjoint extension, with its actual domain.
-/

@[expose] public section

noncomputable section

open scoped BigOperators LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarJointReduction

open HistoryHaarJointHessian HistoryHaarJointCore
open Operations

def fieldInclusion (N : ℕ) : HistoryHaarClosedHessian.Fields N →ₗ[ℂ] Space N where
  toFun A := WithLp.toLp 2 (A, 0)
  map_add' _ _ := by apply (WithLp.equiv 2 _).injective; simp
  map_smul' _ _ := by apply (WithLp.equiv 2 _).injective; simp

def stateInclusion (N : ℕ) : State N →ₗ[ℂ] Space N where
  toFun ψ := WithLp.toLp 2 (0, ψ)
  map_add' _ _ := by apply (WithLp.equiv 2 _).injective; simp
  map_smul' _ _ := by apply (WithLp.equiv 2 _).injective; simp

theorem fieldInclusion_core_mem (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N) :
    fieldInclusion N A.val ∈ ResponseCore N := by
  have hs : HistoryHaarClosedHessian.FieldCore N ≤
      (ResponseCore N).comap (fieldInclusion N) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change fieldInclusion N (HistoryHaarClosedHessian.basis N i) ∈ ResponseCore N
    have he : fieldInclusion N (HistoryHaarClosedHessian.basis N i) = basis N (.inl i) := by
      rw [basis, HilbertBasisProduct.basis_inl]
      rfl
    rw [he]
    exact Submodule.subset_span ⟨.inl i, rfl⟩
  exact hs A.property

def fieldCore (N : ℕ) : HistoryHaarClosedHessian.FieldCore N →ₗ[ℂ] ResponseCore N where
  toFun A := ⟨fieldInclusion N A.val, fieldInclusion_core_mem N A⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The finite state expansion uses its entire original orthonormal basis. -/
def stateCore (N : ℕ) : State N →ₗ[ℂ] ResponseCore N where
  toFun ψ := ∑ i : HistoryCliffordAction.Index N,
    (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ).repr ψ i •
      responseCoreBasis N (.inr i)
  map_add' ψ ξ := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c ψ := by simp [map_smul, Finset.smul_sum, smul_smul]

theorem stateCore_coe (N : ℕ) (ψ : State N) :
    (stateCore N ψ : Space N) = stateInclusion N ψ := by
  change (ResponseCore N).subtype (∑ i,
    (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ).repr ψ i •
      responseCoreBasis N (.inr i)) = _
  rw [map_sum]
  simp only [map_smul]
  have hi (i : HistoryCliffordAction.Index N) :
      ((ResponseCore N).subtype (responseCoreBasis N (.inr i))) =
        stateInclusion N (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ i) := by
    change (FiniteEigenbasisCore.finiteBasis (basis N) (.inr i) : Space N) = _
    rw [FiniteEigenbasisCore.finiteBasis_coe, basis, HilbertBasisProduct.basis_inr]
    change WithLp.toLp 2 (0, stateBasis N i) = WithLp.toLp 2
      (0, EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ i)
    exact congrArg (fun v : State N => WithLp.toLp 2 (0, v))
      (congrFun (OrthonormalBasis.coe_toHilbertBasis
        (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ)) i)
  simp_rw [hi, ← map_smul]
  rw [← map_sum, (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ).sum_repr]

@[simp] theorem coreField_stateCore (N : ℕ) (ψ : State N) :
    coreField N (stateCore N ψ) = 0 := by
  apply Subtype.ext
  change (stateCore N ψ : Space N).fst = 0
  rw [stateCore_coe]
  rfl

@[simp] theorem stateProjection_stateCore (N : ℕ) (ψ : State N) :
    stateProjection N (stateCore N ψ : Space N) = ψ := by
  rw [stateCore_coe]
  rfl

@[simp] theorem coreField_fieldCore (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N) :
    coreField N (fieldCore N A) = A := rfl

@[simp] theorem stateProjection_fieldCore (N : ℕ)
    (A : HistoryHaarClosedHessian.FieldCore N) :
    stateProjection N (fieldCore N A : Space N) = 0 := rfl

private theorem coefficients_zero (N : ℕ) :
    HistoryHaarClosedHessian.coefficients N 0 = 0 := by
  funext i j
  exact map_zero (HistoryHaarClosedHessian.coreComponent N (i, j))

theorem core_decomposition (N : ℕ) (x : ResponseCore N) :
    fieldCore N (coreField N x) + stateCore N (stateProjection N x.val) = x := by
  apply Subtype.ext
  rw [Submodule.coe_add, stateCore_coe]
  change WithLp.toLp 2 (x.val.fst, 0) + WithLp.toLp 2 (0, x.val.snd) = x.val
  apply (WithLp.equiv 2 _).injective
  change (x.val.ofLp.1 + 0, 0 + x.val.ofLp.2) = x.val.ofLp
  exact Prod.ext (add_zero _) (zero_add _)

def normSq (N : ℕ) (x : ResponseCore N) : ℝ := ‖x.val‖ ^ 2

@[simp] theorem normSq_zero (N : ℕ) : normSq N 0 = 0 := by simp [normSq]

/-- The source differential contribution vanishes on homogeneous states. -/
def sourceHodgeEigenvalue (N : ℕ) : Index N → ℝ
  | .inl i => HistoryHaarClosedHessian.eigenvalue N i
  | .inr _ => 0

/-- The defining response acts on the entire homogeneous state sector. -/
def sourceResponseEigenvalue (N : ℕ) : Index N → ℝ
  | .inl _ => 0
  | .inr _ => HistoryDefiningResponse.coefficient N

theorem eigenvalue_source_decomposition (N : ℕ) (i : Index N) :
    eigenvalue N i = sourceHodgeEigenvalue N i + sourceResponseEigenvalue N i := by
  cases i <;> simp [eigenvalue, sourceHodgeEigenvalue, sourceResponseEigenvalue]

def hessianQuadratic (N : ℕ) (x : ResponseCore N) : ℝ :=
  HistoryHaarCoupledAction.quadratic N
    (HistoryHaarClosedHessian.coefficients N (coreField N x))
    (stateProjection N x.val)

def hessianPairing (N : ℕ) (x y : ResponseCore N) : ℝ :=
  HistoryHaarCoupledAction.hessian N
    (HistoryHaarClosedHessian.coefficients N (coreField N x))
    (HistoryHaarClosedHessian.coefficients N (coreField N y))
    (stateProjection N x.val) (stateProjection N y.val)

def quadraticAction (N : ℕ) (x : ResponseCore N) : ℝ := hessianQuadratic N x / 2

theorem hessianQuadratic_operator (N : ℕ) (x : ResponseCore N) :
    hessianQuadratic N x = (inner ℂ x.val (finiteOperator N x)).re :=
  (finiteOperator_energy N x).symm

@[simp] theorem hessianPairing_self (N : ℕ) (x : ResponseCore N) :
    hessianPairing N x x = hessianQuadratic N x :=
  HistoryHaarCoupledAction.hessian_diagonal N _ _

theorem hessianPairing_symm (N : ℕ) (x y : ResponseCore N) :
    hessianPairing N x y = hessianPairing N y x :=
  HistoryHaarCoupledAction.hessian_symm N _ _ _ _

@[simp] theorem hessianQuadratic_zero (N : ℕ) : hessianQuadratic N 0 = 0 := by
  rw [hessianQuadratic_operator]
  simp

theorem hessianQuadratic_field (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N) :
    hessianQuadratic N (fieldCore N A) =
      (inner ℂ A.val (HistoryHaarClosedHessian.finiteOperator N A)).re := by
  change HistoryHaarCoupledAction.quadratic N
    (HistoryHaarClosedHessian.coefficients N A) 0 = _
  rw [HistoryHaarCoupledAction.hessian_operator]
  simp

theorem hessianQuadratic_state (N : ℕ) (ψ : State N) :
    hessianQuadratic N (stateCore N ψ) = HistoryDefiningResponse.coefficient N * ‖ψ‖ ^ 2 := by
  unfold hessianQuadratic
  rw [coreField_stateCore, stateProjection_stateCore, coefficients_zero]
  simp [HistoryHaarCoupledAction.quadratic]

theorem hessianPairing_field_state_zero (N : ℕ)
    (A : HistoryHaarClosedHessian.FieldCore N) (ψ : State N) :
    hessianPairing N (fieldCore N A) (stateCore N ψ) = 0 := by
  unfold hessianPairing
  rw [coreField_fieldCore, coreField_stateCore,
    stateProjection_fieldCore, stateProjection_stateCore, coefficients_zero]
  simp [HistoryHaarCoupledAction.hessian]

theorem hessianQuadratic_decomposition (N : ℕ) (x : ResponseCore N) :
    hessianQuadratic N x =
      hessianQuadratic N (fieldCore N (coreField N x)) +
        hessianQuadratic N (stateCore N (stateProjection N x.val)) := by
  rw [hessianQuadratic_field, hessianQuadratic_state]
  unfold hessianQuadratic
  rw [HistoryHaarCoupledAction.hessian_operator]
  congr 1
  change HistoryDefiningResponse.quadratic N (stateProjection N x.val) = _
  exact HistoryDefiningResponse.quadratic_eq N _

theorem quadraticAction_closed (N : ℕ) (x : ResponseCore N) :
    quadraticAction N x = HistoryHaarJointEquation.action N
      ⟨x.val, (finiteOperator_le_operator N).1 x.property⟩ :=
  (HistoryHaarJointEquation.action_on_core N x).symm

theorem hessianQuadratic_coercive (N : ℕ) (x : ResponseCore N) :
    gapSq N * normSq N x ≤ hessianQuadratic N x := by
  rw [hessianQuadratic_operator]
  have h := sharp_coercivity N ⟨x.val, (finiteOperator_le_operator N).1 x.property⟩
  have he := (finiteOperator_le_operator N).2
    (x := x) (y := ⟨x.val, (finiteOperator_le_operator N).1 x.property⟩) rfl
  simpa only [normSq, ← he] using h

theorem hessianQuadratic_nonneg (N : ℕ) (x : ResponseCore N) :
    0 ≤ hessianQuadratic N x :=
  le_trans (mul_nonneg (le_trans (by norm_num) (gapSq_lower N))
    (sq_nonneg _)) (hessianQuadratic_coercive N x)

theorem normSq_nonneg (N : ℕ) (x : ResponseCore N) : 0 ≤ normSq N x :=
  sq_nonneg _

theorem normSq_eq_zero_iff (N : ℕ) (x : ResponseCore N) :
    normSq N x = 0 ↔ x = 0 := by
  simp only [normSq, sq_eq_zero_iff, norm_eq_zero]
  constructor
  · exact fun h => Subtype.ext h
  · rintro rfl
    rfl

/-- The stationary zero of the actual complete response core is unique.
The assertion uses the derived sharp bound, rather than stipulating a
positive quadratic coefficient in the definition of the core. -/
theorem hessianQuadratic_eq_zero_iff (N : ℕ) (x : ResponseCore N) :
    hessianQuadratic N x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hg : 0 < gapSq N := lt_of_lt_of_le (by norm_num) (gapSq_lower N)
    have hb := hessianQuadratic_coercive N x
    rw [hx] at hb
    have hn : normSq N x ≤ 0 := by
      by_contra hn
      have hp := mul_pos hg (lt_of_not_ge hn)
      linarith
    exact (normSq_eq_zero_iff N x).mp (le_antisymm hn (normSq_nonneg N x))
  · rintro rfl
    rw [hessianQuadratic_operator]
    simp

theorem quadraticAction_unique_minimum (N : ℕ) (x : ResponseCore N) :
    quadraticAction N x = 0 ↔ x = 0 := by
  simp only [quadraticAction, div_eq_zero_iff, show (2 : ℝ) ≠ 0 by norm_num,
    or_false, hessianQuadratic_eq_zero_iff]

/-- A finite witness may retain the nonlinear curvature alongside an
independent complete response-core vector. Both terms use the original
arithmetic fields; this witness does not define the full Hessian. -/
def finiteWitnessAction (N : ℕ) (A : HistoryHaarMatrixCurvature.Coefficients N)
    (x : ResponseCore N) : ℝ :=
  HistoryHaarMatrixCurvature.action N A + quadraticAction N x

theorem finiteWitnessAction_nonneg (N : ℕ)
    (A : HistoryHaarMatrixCurvature.Coefficients N) (x : ResponseCore N) :
    0 ≤ finiteWitnessAction N A x :=
  add_nonneg (HistoryHaarMatrixCurvature.action_nonneg N A)
    (div_nonneg (hessianQuadratic_nonneg N x) (by norm_num))

theorem finiteWitnessAction_coercive (N : ℕ)
    (A : HistoryHaarMatrixCurvature.Coefficients N) (x : ResponseCore N) :
    HistoryHaarMatrixCurvature.action N A + gapSq N * normSq N x / 2 ≤
      finiteWitnessAction N A x := by
  unfold finiteWitnessAction quadraticAction
  exact add_le_add le_rfl (div_le_div_of_nonneg_right
    (hessianQuadratic_coercive N x) (by norm_num : (0 : ℝ) ≤ 2))

theorem hessianQuadratic_minimizer (N : ℕ) :
    hessianQuadratic N (responseCoreBasis N (minimizingIndex N)) = gapSq N := by
  classical
  rw [hessianQuadratic_operator]
  have hi : (responseCoreBasis N (minimizingIndex N) : Space N) =
      basis N (minimizingIndex N) := FiniteEigenbasisCore.finiteBasis_coe _ _
  have he := (finiteOperator_le_operator N).2
    (x := responseCoreBasis N (minimizingIndex N))
    (y := ⟨basis N (minimizingIndex N), basis_mem_domain N _⟩) hi
  rw [he, operator_basis, hi, inner_smul_right,
    orthonormal_iff_ite.mp (basis N).orthonormal, eigenvalue_minimizingIndex]
  simp

structure Conclusions : Prop where
  full_core_decomposition : ∀ N x,
    fieldCore N (coreField N x) + stateCore N (stateProjection N x.val) = x
  actual_differential_energy : ∀ N x,
    hessianQuadratic N x = (inner ℂ x.val (finiteOperator N x)).re
  derived_mixed_zero : ∀ N A ψ, hessianPairing N (fieldCore N A) (stateCore N ψ) = 0
  full_source_decomposition : ∀ N x,
    hessianQuadratic N x =
      hessianQuadratic N (fieldCore N (coreField N x)) +
        hessianQuadratic N (stateCore N (stateProjection N x.val))
  sharp_bound : ∀ N x, gapSq N * normSq N x ≤ hessianQuadratic N x
  exact_bottom : ∀ N,
    hessianQuadratic N (responseCoreBasis N (minimizingIndex N)) = gapSq N
  zero_kernel : ∀ N x, hessianQuadratic N x = 0 ↔ x = 0
  unique_zero_minimum : ∀ N x, quadraticAction N x = 0 ↔ x = 0

theorem generated : Conclusions where
  full_core_decomposition := core_decomposition
  actual_differential_energy := hessianQuadratic_operator
  derived_mixed_zero := hessianPairing_field_state_zero
  full_source_decomposition := hessianQuadratic_decomposition
  sharp_bound := hessianQuadratic_coercive
  exact_bottom := hessianQuadratic_minimizer
  zero_kernel := hessianQuadratic_eq_zero_iff
  unique_zero_minimum := quadraticAction_unique_minimum

end GeneratedFoundations.Arithmetic.HistoryHaarJointReduction
