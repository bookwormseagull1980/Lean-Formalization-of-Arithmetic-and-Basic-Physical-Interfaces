module

public import GeneratedFoundations.Geometry.SourceDirectionalGenerator
public import GeneratedFoundations.Geometry.SourceDirectionalStep
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Arbitrary directional source steps in the actual homogeneous representations

The infinitesimal action is obtained by differentiating the original polynomial
substitution. Polynomial evaluations span the dual of each homogeneous carrier;
this gives the derivative in its already constructed Haar Hilbert realization.
The three axis identifications then follow from uniqueness of the derivatives
of the same source curves. Linearity determines every real source direction.
Finally, uniqueness for a bounded linear ODE proves compatibility with the
operator exponential. No infinitesimal representation is an input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourceCoefficientDifferentiation

namespace GeneratedFoundations.Geometry.SourceDirectionalRepresentation

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

local instance (m : ℕ) : NormedRing (SourceDirectionalGenerator.End m) :=
  ContinuousLinearMap.toNormedRing

local instance (m : ℕ) : NormedAlgebra ℂ (SourceDirectionalGenerator.End m) :=
  ContinuousLinearMap.toNormedAlgebra

local instance (m : ℕ) : NormedAlgebra ℝ (SourceDirectionalGenerator.End m) :=
  .restrictScalars ℝ ℂ (SourceDirectionalGenerator.End m)

local instance (m : ℕ) : NormedAlgebra ℚ (SourceDirectionalGenerator.End m) :=
  .restrictScalars ℚ ℝ (SourceDirectionalGenerator.End m)

/-- Evaluation is restricted to the original homogeneous subspace. -/
def evaluation (m : ℕ) (x : Fin 2 → ℂ) : Module.Dual ℂ (Carrier m) :=
  (MvPolynomial.aeval x).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m).subtype

@[simp] theorem evaluation_apply (m : ℕ) (x : Fin 2 → ℂ) (p : Carrier m) :
    evaluation m x p = MvPolynomial.aeval x (p : PolynomialSpace) := rfl

/-- Separation by actual evaluations, not by an assumed set of coordinates. -/
theorem evaluation_span (m : ℕ) :
    Submodule.span ℂ (Set.range (evaluation m)) = ⊤ := by
  let W := Submodule.span ℂ (Set.range (evaluation m))
  have hW : W.dualCoannihilator = ⊥ := by
    apply bot_unique
    intro p hp
    apply (Submodule.mem_bot ℂ).mpr
    apply Subtype.ext
    apply p.property.eq_zero_of_forall_eval_eq_zero
    intro x
    exact (Submodule.mem_dualCoannihilator p).mp hp (evaluation m x)
      (Submodule.subset_span ⟨x, rfl⟩)
  calc
    W = W.dualCoannihilator.dualAnnihilator :=
      Subspace.dualCoannihilator_dualAnnihilator_eq.symm
    _ = ⊤ := by rw [hW, Submodule.dualAnnihilator_bot]

/-- The ordinary chain rule is proved on the actual polynomial expression. -/
theorem polynomial_eval_hasDerivAt (p : PolynomialSpace)
    (v : ℝ → Fin 2 → ℂ) (v' : Fin 2 → ℂ) (t : ℝ)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (v' i) t) :
    HasDerivAt (fun s => MvPolynomial.aeval (v s) p)
      (∑ i : Fin 2, v' i * MvPolynomial.aeval (v t) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa [pderiv_C] using hasDerivAt_const t c
  | add p q hp hq =>
      convert hp.add hq using 1
      · funext s
        exact map_add (MvPolynomial.aeval (v s)) p q
      · simp only [map_add, Fin.sum_univ_two]
        ring
  | mul_X p i hp =>
      convert hp.mul (hv i) using 1
      · funext s
        simp only [Pi.mul_apply, map_mul, MvPolynomial.aeval_X]
      · fin_cases i <;>
          simp [Fin.sum_univ_two] <;> ring

theorem eval_polynomialAction (M : Mat2) (x : Fin 2 → ℂ) (p : PolynomialSpace) :
    MvPolynomial.aeval x (polynomialAction M p) =
      MvPolynomial.aeval (fun i => ∑ j : Fin 2, M j i * x j) p := by
  have h : (MvPolynomial.aeval x).comp (polynomialAction M) =
      MvPolynomial.aeval (fun i => ∑ j : Fin 2, M j i * x j) := by
    ext i
    simp [variableImage]
  exact AlgHom.congr_fun h p

/-- The column substitution fixes the order of the two matrix indices. -/
def matrixDifferential (m : ℕ) : Mat2 →ₗ[ℂ] Module.End ℂ (Carrier m) where
  toFun M := ∑ i : Fin 2, ∑ j : Fin 2, M j i • transfer m j i
  map_add' M N := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem evaluation_action_hasDerivAt (m : ℕ) (p : Carrier m) (x : Fin 2 → ℂ)
    (M : ℝ → Mat2) (M' : Mat2) (t : ℝ) (hM : HasDerivAt M M' t)
    (hMt : M t = 1) :
    HasDerivAt (fun s => evaluation m x (degreeAction m (M s) p))
      (evaluation m x (matrixDifferential m M' p)) t := by
  have hv : ∀ i : Fin 2,
      HasDerivAt (fun s => ∑ j : Fin 2, M s j i * x j)
        (∑ j : Fin 2, M' j i * x j) t := by
    intro i
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hM j)) i).mul_const (x j)
  have h := polynomial_eval_hasDerivAt (p : PolynomialSpace)
    (fun s i => ∑ j : Fin 2, M s j i * x j)
    (fun i => ∑ j : Fin 2, M' j i * x j) t hv
  have hx : (fun i => ∑ j : Fin 2, M t j i * x j) = x := by
    rw [hMt]
    funext i
    simp only [Matrix.one_apply]
    fin_cases i <;> simp
  rw [hx] at h
  have hf : (fun s => evaluation m x (degreeAction m (M s) p)) =
      fun s => MvPolynomial.aeval (fun i => ∑ j : Fin 2, M s j i * x j)
        (p : PolynomialSpace) := by
    funext s
    exact eval_polynomialAction (M s) x p
  rw [hf]
  convert h using 1
  simp [evaluation, matrixDifferential, transfer_coe, Fin.sum_univ_two]
  ring

/-- Finite-dimensional duality transports the scalar chain rule to every
linear functional without any norm on the infinite polynomial algebra. -/
theorem functional_action_hasDerivAt (m : ℕ) (p : Carrier m)
    (φ : Module.Dual ℂ (Carrier m)) (M : ℝ → Mat2) (M' : Mat2) (t : ℝ)
    (hM : HasDerivAt M M' t) (hMt : M t = 1) :
    HasDerivAt (fun s => φ (degreeAction m (M s) p))
      (φ (matrixDifferential m M' p)) t := by
  have hφ : φ ∈ Submodule.span ℂ (Set.range (evaluation m)) := by
    rw [evaluation_span]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun ψ _ =>
    HasDerivAt (fun s => ψ (degreeAction m (M s) p))
      (ψ (matrixDifferential m M' p)) t) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨x, rfl⟩
    exact evaluation_action_hasDerivAt m p x M M' t hM hMt
  · simpa using hasDerivAt_const t (0 : ℂ)
  · intro φ ψ _ _ hφ hψ
    simpa only [LinearMap.add_apply, Pi.add_apply] using! hφ.add hψ
  · intro c φ _ hφ
    simpa only [LinearMap.smul_apply, smul_eq_mul] using hφ.const_mul c

theorem hilbertCoordinate_symm_coefficient (m : ℕ) (p : Carrier m) :
    (hilbertCoordinate m).symm (coefficientVector m p) = carrierEquiv m p := by
  change carrierEquiv m ((coefficientEquiv m).symm (coefficientEquiv m p)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Differentiation lands in the existing Haar realization of the same vector. -/
theorem polynomial_action_hilbert_hasDerivAt (m : ℕ) (p : Carrier m)
    (M : ℝ → Mat2) (M' : Mat2) (t : ℝ)
    (hM : HasDerivAt M M' t) (hMt : M t = 1) :
    HasDerivAt (fun s => carrierEquiv m (degreeAction m (M s) p))
      (carrierEquiv m (matrixDifferential m M' p)) t := by
  have hc : HasDerivAt
      (fun s => fun k : Fin (m + 1) =>
        ((degreeAction m (M s) p : Carrier m) : PolynomialSpace).coeff
          (exponentOfIndex m k).val)
      (fun k : Fin (m + 1) =>
        ((matrixDifferential m M' p : Carrier m) : PolynomialSpace).coeff
          (exponentOfIndex m k).val) t := by
    apply hasDerivAt_pi.mpr
    intro k
    exact functional_action_hasDerivAt m p
      ((MvPolynomial.lcoeff ℂ (exponentOfIndex m k).val).comp
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m).subtype) M M' t hM hMt
  have hc' := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hc
  change HasDerivAt (fun s => coefficientVector m (degreeAction m (M s) p))
    (coefficientVector m (matrixDifferential m M' p)) t at hc'
  have hh := ((hilbertCoordinate m).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hc'
  change HasDerivAt
    (fun s => (hilbertCoordinate m).symm
      (coefficientVector m (degreeAction m (M s) p)))
    ((hilbertCoordinate m).symm
      (coefficientVector m (matrixDifferential m M' p))) t at hh
  simpa only [hilbertCoordinate_symm_coefficient] using hh

/-- The matrix and Hilbert derivatives of each original axis agree by
uniqueness. Thus signs and half-angle factors come from the same curve. -/
theorem matrixDifferential_axis (m : ℕ) (a : Fin 3) (p : Carrier m) :
    carrierEquiv m (matrixDifferential m (SourceAxisMetric.axisVelocity a) p) =
      hilbertAxis m a (carrierEquiv m p) := by
  have h := polynomial_action_hilbert_hasDerivAt m p
    (fun t => (sourceAxis a t : Mat2)) (SourceAxisMetric.axisVelocity a) 0
    (SourceAxisMetric.axisCurve_hasDerivAt_zero a)
    (by rw [sourceAxis_zero]; rfl)
  have h' := sourceAxis_hasDerivAt m a (carrierEquiv m p) 0
  simp only [sourceAxis_zero, unitaryAction_one_apply] at h'
  have hf : (fun t => carrierEquiv m (degreeAction m (sourceAxis a t : Mat2) p)) =
      fun t => unitaryAction m (sourceAxis a t) (carrierEquiv m p) := by
    funext t
    exact (unitaryAction_apply_carrier m (sourceAxis a t) p).symm
  rw [hf] at h
  exact h.unique h'

/-- The actual arbitrary-direction derivative is the previously defined
bounded generator; no independent choice of infinitesimal action is made. -/
theorem matrixDifferential_direction (m : ℕ) (ξ : Fin 3 → ℝ) (p : Carrier m) :
    carrierEquiv m (matrixDifferential m (SourceDirectionalStep.generator ξ) p) =
      SourceDirectionalGenerator.generator m ξ (carrierEquiv m p) := by
  simp only [SourceDirectionalStep.generator, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, matrixDifferential_axis,
    SourceDirectionalGenerator.generator_apply]

theorem directional_orbit_hasDerivAt_zero (m : ℕ) (ξ : Fin 3 → ℝ)
    (v : HilbertCarrier m) :
    HasDerivAt (fun t => unitaryAction m (SourceDirectionalStep.step ξ t) v)
      (SourceDirectionalGenerator.generator m ξ v) 0 := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  have h := polynomial_action_hilbert_hasDerivAt m p
    (fun t => (SourceDirectionalStep.step ξ t : Mat2))
    (SourceDirectionalStep.generator ξ) 0
    (SourceDirectionalStep.step_hasDerivAt_zero ξ)
    (by rw [SourceDirectionalStep.step_zero]; rfl)
  have hf : (fun t => carrierEquiv m
      (degreeAction m (SourceDirectionalStep.step ξ t : Mat2) p)) =
      fun t => unitaryAction m (SourceDirectionalStep.step ξ t) (carrierEquiv m p) := by
    funext t
    exact (unitaryAction_apply_carrier m (SourceDirectionalStep.step ξ t) p).symm
  rw [hf] at h
  simpa only [matrixDifferential_direction] using h

/-- The source group law gives the linear ODE at every parameter. -/
theorem directional_orbit_hasDerivAt (m : ℕ) (ξ : Fin 3 → ℝ)
    (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s => unitaryAction m (SourceDirectionalStep.step ξ s) v)
      (SourceDirectionalGenerator.generator m ξ
        (unitaryAction m (SourceDirectionalStep.step ξ t) v)) t := by
  have h := directional_orbit_hasDerivAt_zero m ξ
    (unitaryAction m (SourceDirectionalStep.step ξ t) v)
  have hshift : HasDerivAt
      (fun s => unitaryAction m (SourceDirectionalStep.step ξ (s - t))
        (unitaryAction m (SourceDirectionalStep.step ξ t) v))
      (SourceDirectionalGenerator.generator m ξ
        (unitaryAction m (SourceDirectionalStep.step ξ t) v)) t := by
    have h0 : HasDerivAt
        (fun s => unitaryAction m (SourceDirectionalStep.step ξ s)
          (unitaryAction m (SourceDirectionalStep.step ξ t) v))
        (SourceDirectionalGenerator.generator m ξ
          (unitaryAction m (SourceDirectionalStep.step ξ t) v)) (t - t) := by
      simpa only [sub_self] using! h
    simpa using! HasDerivAt.comp_sub_const t t h0
  have hf : (fun s => unitaryAction m (SourceDirectionalStep.step ξ (s - t))
      (unitaryAction m (SourceDirectionalStep.step ξ t) v)) =
      fun s => unitaryAction m (SourceDirectionalStep.step ξ s) v := by
    funext s
    rw [← unitaryAction_mul_apply, ← SourceDirectionalStep.step_add, sub_add_cancel]
  rwa [hf] at hshift

theorem exponential_orbit_hasDerivAt (m : ℕ) (ξ : Fin 3 → ℝ)
    (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • SourceDirectionalGenerator.generator m ξ) v)
      (SourceDirectionalGenerator.generator m ξ
        (NormedSpace.exp ((t : ℂ) • SourceDirectionalGenerator.generator m ξ) v)) t := by
  have h := _root_.hasDerivAt_exp_smul_const'
    (SourceDirectionalGenerator.generator m ξ) t
  have hv := ((ContinuousLinearMap.apply ℂ (HilbertCarrier m) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt
    (fun s : ℝ => NormedSpace.exp (s • SourceDirectionalGenerator.generator m ξ) v)
    ((SourceDirectionalGenerator.generator m ξ *
      NormedSpace.exp (t • SourceDirectionalGenerator.generator m ξ)) v) t at hv
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    mul_apply_eq_comp] using! hv

/-- Compatibility of the genuine source operation with the exponential on
every actual homogeneous Haar Hilbert carrier. -/
theorem unitaryAction_step_eq_exp (m : ℕ) (ξ : Fin 3 → ℝ) (t : ℝ)
    (v : HilbertCarrier m) :
    unitaryAction m (SourceDirectionalStep.step ξ t) v =
      NormedSpace.exp ((t : ℂ) • SourceDirectionalGenerator.generator m ξ) v := by
  have h := ODE_solution_unique_univ
    (s := fun _ : ℝ => Set.univ)
    (v := fun _ : ℝ => SourceDirectionalGenerator.generator m ξ)
    (t₀ := (0 : ℝ))
    (fun _ => (SourceDirectionalGenerator.generator m ξ).lipschitzWith.lipschitzOnWith)
    (fun s => ⟨directional_orbit_hasDerivAt m ξ v s, Set.mem_univ _⟩)
    (fun s => ⟨exponential_orbit_hasDerivAt m ξ v s, Set.mem_univ _⟩)
    (by simp [SourceDirectionalStep.step_zero, unitaryAction_one_apply])
  exact congrFun h t

theorem unitaryAction_step_eq_exp_clm (m : ℕ) (ξ : Fin 3 → ℝ) (t : ℝ) :
    (unitaryAction m (SourceDirectionalStep.step ξ t)).toLinearIsometry.toContinuousLinearMap =
      NormedSpace.exp ((t : ℂ) • SourceDirectionalGenerator.generator m ξ) := by
  apply ContinuousLinearMap.ext
  intro v
  exact unitaryAction_step_eq_exp m ξ t v

end GeneratedFoundations.Geometry.SourceDirectionalRepresentation
