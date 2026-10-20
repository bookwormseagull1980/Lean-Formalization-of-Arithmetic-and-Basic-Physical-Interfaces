module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Phase evolution of a complete finite coefficient carrier

Real weights on an actual finite orthonormal coefficient space determine
both a self-adjoint generator and its continuous unitary group. The
exponential identity is proved in the normed algebra of continuous
endomorphisms. This common comparison theorem is instantiated with the
weights already generated in each branch; it supplies no new root data.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.FinitePhaseFlow

variable {ι : Type*}

abbrev Space (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι

def phase (q : ι → ℝ) (t : ℝ) (i : ι) : ℂ :=
  Complex.exp ((Complex.I * (q i : ℂ)) * (t : ℂ))

@[simp] theorem phase_zero (q : ι → ℝ) (i : ι) : phase q 0 i = 1 := by
  simp [phase]

theorem phase_add (q : ι → ℝ) (s t : ℝ) (i : ι) :
    phase q (s + t) i = phase q s i * phase q t i := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem phase_norm (q : ι → ℝ) (t : ℝ) (i : ι) : ‖phase q t i‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem phase_neg_mul (q : ι → ℝ) (t : ℝ) (i : ι) :
    phase q (-t) i * phase q t i = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

theorem phase_hasDerivAt (q : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun s : ℝ => phase q s i)
      ((Complex.I * (q i : ℂ)) * phase q t i) t := by
  have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := t))
  simpa only [phase, mul_one, one_mul, mul_comm] using
    (hr.const_mul (Complex.I * (q i : ℂ))).cexp

variable [Fintype ι]

def flow (q : ι → ℝ) (t : ℝ) : Module.End ℂ (Space ι) where
  toFun x := WithLp.toLp 2 fun i => phase q t i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

@[simp] theorem flow_apply (q : ι → ℝ) (t : ℝ) (x : Space ι) (i : ι) :
    flow q t x i = phase q t i * x i := rfl

@[simp] theorem flow_zero (q : ι → ℝ) : flow q 0 = 1 := by
  ext x i
  simp

theorem flow_add (q : ι → ℝ) (s t : ℝ) :
    flow q (s + t) = flow q s * flow q t := by
  ext x i
  simp [phase_add, mul_assoc]

theorem flow_inverse (q : ι → ℝ) (t : ℝ) : flow q (-t) * flow q t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem flow_norm (q : ι → ℝ) (t : ℝ) (x : Space ι) : ‖flow q t x‖ = ‖x‖ := by
  have hs : ‖flow q t x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2]
  nlinarith [norm_nonneg (flow q t x), norm_nonneg x]

def unitary (q : ι → ℝ) (t : ℝ) : Space ι ≃ₗᵢ[ℂ] Space ι where
  toFun := flow q t
  invFun := flow q (-t)
  left_inv x := LinearMap.congr_fun (flow_inverse q t) x
  right_inv x := by
    have h := LinearMap.congr_fun (flow_inverse q (-t)) x
    change (flow q t * flow q (-t)) x = (1 : Module.End ℂ (Space ι)) x
    simpa only [neg_neg] using h
  map_add' := (flow q t).map_add
  map_smul' := (flow q t).map_smul
  norm_map' := flow_norm q t

theorem flow_inner (q : ι → ℝ) (t : ℝ) (x y : Space ι) :
    inner ℂ (flow q t x) (flow q t y) = inner ℂ x y :=
  (unitary q t).inner_map_map x y

theorem flow_continuous (q : ι → ℝ) (x : Space ι) :
    Continuous (fun t : ℝ => flow q t x) := by
  change Continuous (fun t : ℝ => WithLp.toLp 2 fun i => phase q t i * x i)
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).comp
  apply continuous_pi
  intro i
  exact (continuous_iff_continuousAt.mpr fun t =>
    (phase_hasDerivAt q t i).continuousAt).mul continuous_const

def generator (q : ι → ℝ) : Module.End ℂ (Space ι) where
  toFun x := WithLp.toLp 2 fun i => (q i : ℂ) * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

@[simp] theorem generator_apply (q : ι → ℝ) (x : Space ι) (i : ι) :
    generator q x i = (q i : ℂ) * x i := rfl

theorem generator_adjoint (q : ι → ℝ) : (generator q).adjoint = generator q := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', generator_apply,
    map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem flow_hasDerivAt_coordinate (q : ι → ℝ) (t : ℝ) (x : Space ι) (i : ι) :
    HasDerivAt (fun s : ℝ => flow q s x i)
      (Complex.I * generator q (flow q t x) i) t := by
  simpa only [flow_apply, generator_apply, mul_assoc] using
    (phase_hasDerivAt q t i).mul_const (x i)

abbrev End (ι : Type*) [Fintype ι] := Space ι →L[ℂ] Space ι

local instance : NormedRing (End ι) := ContinuousLinearMap.toNormedRing
local instance : NormedAlgebra ℂ (End ι) := ContinuousLinearMap.toNormedAlgebra
local instance : IsTopologicalRing (End ι) := NonUnitalSeminormedRing.toIsTopologicalRing

def continuousModel : Module.End ℂ (Space ι) ≃ₐ[ℂ] End ι :=
  Module.End.toContinuousLinearMap (Space ι)

@[simp] theorem continuousModel_apply (A : Module.End ℂ (Space ι)) (x : Space ι) :
    continuousModel A x = A x := rfl

variable [DecidableEq ι]

def matrixModel : Matrix ι ι ℂ ≃ₐ[ℂ] End ι :=
  (Matrix.toLinAlgEquiv'.trans
    ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.conjAlgEquiv ℂ)).trans continuousModel

@[simp] theorem matrixModel_apply (A : Matrix ι ι ℂ) (x : Space ι) (i : ι) :
    matrixModel A x i = ∑ j, A i j * x j := rfl

theorem matrixModel_diagonal (q : ι → ℝ) :
    matrixModel (Matrix.diagonal fun i => (q i : ℂ)) = continuousModel (generator q) := by
  ext x i
  simp [Matrix.diagonal]

theorem map_exp {A B : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Ring B] [Algebra ℂ B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
    (f : A →ₐ[ℂ] B) (hf : Continuous f) (a : A) :
    f (NormedSpace.exp a) = NormedSpace.exp (f a) := by
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  refine ((NormedSpace.expSeries_summable' (𝕂 := ℂ) a).hasSum.map f hf).tsum_eq.symm.trans ?_
  apply tsum_congr
  intro n
  simp only [Function.comp_def, map_smul, map_pow]

theorem flow_eq_exp (q : ι → ℝ) (t : ℝ) :
    continuousModel (flow q t) =
      NormedSpace.exp ((Complex.I * (t : ℂ)) • continuousModel (generator q)) := by
  have hf : Continuous (matrixModel (ι := ι)) :=
    (matrixModel (ι := ι)).toLinearMap.continuous_of_finiteDimensional
  have he := map_exp (matrixModel (ι := ι)).toAlgHom hf
    ((Complex.I * (t : ℂ)) • Matrix.diagonal (fun i => (q i : ℂ)))
  change matrixModel (NormedSpace.exp
    ((Complex.I * (t : ℂ)) • Matrix.diagonal (fun i => (q i : ℂ)))) =
    NormedSpace.exp (matrixModel
      ((Complex.I * (t : ℂ)) • Matrix.diagonal (fun i => (q i : ℂ)))) at he
  rw [map_smul, matrixModel_diagonal] at he
  rw [← he, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext x i
  simp [Matrix.diagonal, phase, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ,
    mul_comm, mul_left_comm]

end GeneratedFoundations.Operations.FinitePhaseFlow
