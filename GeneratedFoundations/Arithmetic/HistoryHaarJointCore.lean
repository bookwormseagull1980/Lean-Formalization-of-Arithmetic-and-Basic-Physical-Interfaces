module

public import GeneratedFoundations.Arithmetic.HistoryHaarJointHessian

/-!
# Differential core of the joint arithmetic Haar Hessian

Projection of a finite joint field onto its matrix-field factor belongs
to the original differential core. This is proved from the complete joint
basis, not imposed on the input. The finite spectral operator is then
identified with the actual twice-curl field operator and defining-state
response. Its quadratic form is the second variation of the nonlinear
coupled action on every vector of this core.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryHaarJointCore

open HistoryHaarJointHessian
open Operations

abbrev ResponseCore (N : ℕ) := FiniteEigenbasisCore.finiteSpan (basis N)

def responseCoreBasis (N : ℕ) : Module.Basis (Index N) ℂ (ResponseCore N) :=
  FiniteEigenbasisCore.finiteBasis (basis N)

def stateProjection (N : ℕ) : Space N →ₗ[ℂ] State N where
  toFun x := x.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fieldProjection (N : ℕ) : Space N →ₗ[ℂ] HistoryHaarClosedHessian.Fields N where
  toFun x := x.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem stateProjection_basis (N : ℕ) (i : Index N) :
    stateProjection N (responseCoreBasis N i) =
      Sum.elim (fun _ => 0) (stateBasis N) i := by
  rw [responseCoreBasis, FiniteEigenbasisCore.finiteBasis_coe]
  cases i with
  | inl a =>
    rw [basis, HilbertBasisProduct.basis_inl]
    rfl
  | inr a =>
    rw [basis, HilbertBasisProduct.basis_inr]
    rfl

theorem fieldProjection_core_mem (N : ℕ) (x : ResponseCore N) :
    fieldProjection N x.val ∈ HistoryHaarClosedHessian.FieldCore N := by
  have hs : ResponseCore N ≤
      (HistoryHaarClosedHessian.FieldCore N).comap (fieldProjection N) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change fieldProjection N (basis N i) ∈ HistoryHaarClosedHessian.FieldCore N
    cases i with
    | inl a =>
      rw [basis, HilbertBasisProduct.basis_inl]
      change HistoryHaarClosedHessian.basis N a ∈ HistoryHaarClosedHessian.FieldCore N
      exact FiniteEigenbasisCore.basis_mem_domain (HistoryHaarClosedHessian.basis N)
        (HistoryHaarClosedHessian.eigenvalue N) a
    | inr a =>
      rw [basis, HilbertBasisProduct.basis_inr]
      exact (HistoryHaarClosedHessian.FieldCore N).zero_mem
  exact hs x.property

def coreField (N : ℕ) : ResponseCore N →ₗ[ℂ] HistoryHaarClosedHessian.FieldCore N where
  toFun x := ⟨fieldProjection N x.val, fieldProjection_core_mem N x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def differentialCore (N : ℕ) : ResponseCore N →ₗ[ℂ] Space N :=
  (WithLp.linearEquiv 2 ℂ (HistoryHaarClosedHessian.Fields N × State N)).symm.toLinearMap.comp
    (((HistoryHaarClosedHessian.finiteOperator N).toFun.comp (coreField N)).prod
      ((HistoryDefiningResponse.response N).comp
        ((stateProjection N).comp (ResponseCore N).subtype)))

theorem finiteOperator_eq_differentialCore (N : ℕ) :
    (finiteOperator N).toFun = differentialCore N := by
  apply LinearMap.ext
  intro x
  have hx := FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)
  let y : (operator N).domain := ⟨x.val, hx.1 x.property⟩
  have he : operator N y = finiteOperator N x := (hx.2 (x := x) (y := y) rfl).symm
  change finiteOperator N x = differentialCore N x
  rw [← he, operator_components]
  have hc := FiniteEigenbasisCore.le_closure (HistoryHaarClosedHessian.basis N)
    (HistoryHaarClosedHessian.eigenvalue N)
  congr 1
  exact Prod.ext ((hc.2 (x := coreField N x) (y :=
    ⟨x.val.fst, (domain_iff N x.val).mp y.property⟩) rfl).symm) rfl

theorem finiteOperator_energy (N : ℕ) (x : ResponseCore N) :
    (inner ℂ (x : Space N) (finiteOperator N x)).re =
      HistoryHaarCoupledAction.quadratic N
        (HistoryHaarClosedHessian.coefficients N (coreField N x))
        (stateProjection N x.val) := by
  have he := LinearMap.congr_fun (finiteOperator_eq_differentialCore N) x
  change finiteOperator N x = differentialCore N x at he
  rw [he, WithLp.prod_inner_apply, Complex.add_re]
  change (inner ℂ ((coreField N x : HistoryHaarClosedHessian.FieldCore N) :
      HistoryHaarClosedHessian.Fields N)
      (HistoryHaarClosedHessian.finiteOperator N (coreField N x))).re +
    (inner ℂ (stateProjection N x.val)
      (HistoryDefiningResponse.response N (stateProjection N x.val))).re = _
  rw [HistoryHaarCoupledAction.quadratic, HistoryHaarClosedHessian.finiteOperator_energy]
  exact congrArg (fun r : ℝ =>
    ‖HistoryHaarMatrixCurvature.differentiated N
      (HistoryHaarClosedHessian.coefficients N (coreField N x))‖ ^ 2 + r)
    (HistoryDefiningResponse.quadratic_eq N (stateProjection N x.val))

theorem action_secondDeriv (N : ℕ) (x : ResponseCore N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarCoupledAction.action N
        ((s : ℂ) • HistoryHaarClosedHessian.coefficients N (coreField N x))
        ((s : ℂ) • stateProjection N x.val)) t)
      (inner ℂ (x : Space N) (finiteOperator N x)).re 0 := by
  rw [finiteOperator_energy]
  exact HistoryHaarCoupledAction.secondDeriv_zero N _ _

structure Conclusions : Prop where
  finite_differential : ∀ N, (finiteOperator N).toFun = differentialCore N
  actual_quadratic : ∀ N (x : ResponseCore N),
    (inner ℂ (x : Space N) (finiteOperator N x)).re =
      HistoryHaarCoupledAction.quadratic N
        (HistoryHaarClosedHessian.coefficients N (coreField N x))
        (stateProjection N x.val)
  actual_second_variation : ∀ N (x : ResponseCore N),
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarCoupledAction.action N
        ((s : ℂ) • HistoryHaarClosedHessian.coefficients N (coreField N x))
        ((s : ℂ) • stateProjection N x.val)) t)
      (inner ℂ (x : Space N) (finiteOperator N x)).re 0

theorem generated : Conclusions where
  finite_differential := finiteOperator_eq_differentialCore
  actual_quadratic := finiteOperator_energy
  actual_second_variation := action_secondDeriv

end GeneratedFoundations.Arithmetic.HistoryHaarJointCore
