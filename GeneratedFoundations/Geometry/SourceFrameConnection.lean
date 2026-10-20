module

public import GeneratedFoundations.Geometry.HermitianFrames
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Passive connection covariance in local response frames

On a real coordinate patch, the connection form is a real-linear
one-form with values in complex-linear operators on the model fiber.
For the passive convention `e' = e g`, the transformation is derived
from the actual derivative of `g f`, where `f` denotes the new
components. Covariance for all local sections uniquely determines this
transformation. Its composition law agrees with the overlap cocycle.

The formulas apply on a coordinate neighborhood inside an overlap.
Differentiability is required only there, at the point under study;
the response bundle need not possess a global frame.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.SourceFrameConnection

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev FiberEnd := H →L[ℂ] H
abbrev ConnectionForm := B →L[ℝ] FiberEnd (H := H)

/-- An affine change of the one-form, with a specified derivative of the frame change. -/
def transformedForm (g : H ≃L[ℂ] H)
    (dg A : ConnectionForm (B := B) (H := H)) : ConnectionForm (B := B) (H := H) :=
  ((ContinuousLinearMap.mul ℝ (FiberEnd (H := H))) g.symm.toContinuousLinearMap).comp
    (((ContinuousLinearMap.mul ℝ (FiberEnd (H := H))).flip g.toContinuousLinearMap).comp A + dg)

@[simp] theorem transformedForm_apply (g : H ≃L[ℂ] H)
    (dg A : ConnectionForm (B := B) (H := H)) (v : B) (w : H) :
    transformedForm g dg A v w = g.symm (A v (g w) + dg v w) := rfl

theorem transformedForm_operator (g : H ≃L[ℂ] H)
    (dg A : ConnectionForm (B := B) (H := H)) (v : B) :
    transformedForm g dg A v =
      g.symm.toContinuousLinearMap * A v * g.toContinuousLinearMap +
        g.symm.toContinuousLinearMap * dg v := by
  ext w
  simp [transformedForm_apply, map_add]

def covariantAt (A : ConnectionForm (B := B) (H := H))
    (f : B → H) (x v : B) : H := fderiv ℝ f x v + A v (f x)

/-- Real differentiation of a complex-linear operator applied to a section. -/
theorem apply_fderiv {G : B → FiberEnd (H := H)}
    {dG : ConnectionForm (B := B) (H := H)} {f : B → H}
    {df : B →L[ℝ] H} {x : B}
    (hG : HasFDerivAt G dG x) (hf : HasFDerivAt f df x) (v : B) :
    fderiv ℝ (fun y => G y (f y)) x v = G x (df v) + dG v (f x) := by
  let r := ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ
  have hr := r.hasFDerivAt.comp x hG
  have h := hr.clm_apply hf
  have hv := congrArg (fun L : B →L[ℝ] H => L v) h.fderiv
  exact hv

/-- Covariance determines the sign of the inhomogeneous term in the passive convention. -/
theorem covariantAt_transformed {G : B → FiberEnd (H := H)}
    {dG : ConnectionForm (B := B) (H := H)} {f : B → H}
    {df : B →L[ℝ] H} {x : B}
    (g : H ≃L[ℂ] H) (hG : HasFDerivAt G dG x)
    (hg : G x = g.toContinuousLinearMap) (hf : HasFDerivAt f df x)
    (A : ConnectionForm (B := B) (H := H)) (v : B) :
    covariantAt (transformedForm g dG A) f x v =
      g.symm (covariantAt A (fun y => G y (f y)) x v) := by
  rw [covariantAt, covariantAt, transformedForm_apply,
    apply_fderiv hG hf, hf.fderiv, hg]
  simp only [map_add]
  rw [show g.symm (g.toContinuousLinearMap (df v)) = df v from g.symm_apply_apply (df v)]
  simp only [ContinuousLinearEquiv.coe_coe]
  abel

theorem transformedForm_unique {G : B → FiberEnd (H := H)}
    {dG : ConnectionForm (B := B) (H := H)} {x : B}
    (g : H ≃L[ℂ] H) (hG : HasFDerivAt G dG x)
    (hg : G x = g.toContinuousLinearMap)
    (A A' : ConnectionForm (B := B) (H := H))
    (hA' : ∀ (f : B → H), DifferentiableAt ℝ f x → ∀ v,
      covariantAt A' f x v = g.symm (covariantAt A (fun y => G y (f y)) x v)) :
    A' = transformedForm g dG A := by
  ext v w
  have h := hA' (fun _ => w) (differentiableAt_const w) v
  have hc := covariantAt_transformed g hG hg (hasFDerivAt_const w x) A v
  have he := h.trans hc.symm
  exact add_left_cancel he

/-- The derivative of a successive frame change is the noncommutative product rule. -/
def productDerivative (g h : H ≃L[ℂ] H)
    (dg dh : ConnectionForm (B := B) (H := H)) : ConnectionForm (B := B) (H := H) :=
  ((ContinuousLinearMap.mul ℝ (FiberEnd (H := H))) g.toContinuousLinearMap).comp dh +
    ((ContinuousLinearMap.mul ℝ (FiberEnd (H := H))).flip h.toContinuousLinearMap).comp dg

@[simp] theorem productDerivative_apply (g h : H ≃L[ℂ] H)
    (dg dh : ConnectionForm (B := B) (H := H)) (v : B) (w : H) :
    productDerivative g h dg dh v w = g (dh v w) + dg v (h w) := rfl

theorem productDerivative_hasFDerivAt {G K : B → FiberEnd (H := H)}
    {dG dK : ConnectionForm (B := B) (H := H)} {x : B}
    (g h : H ≃L[ℂ] H) (hG : HasFDerivAt G dG x) (hK : HasFDerivAt K dK x)
    (hg : G x = g.toContinuousLinearMap) (hk : K x = h.toContinuousLinearMap) :
    HasFDerivAt (fun y => G y * K y) (productDerivative g h dG dK) x := by
  convert hG.mul' hK using 1
  ext v w
  simp [productDerivative_apply, hg, hk]

/-- Successive affine changes respect the same order as the frame cocycle. -/
theorem transformedForm_trans (g h : H ≃L[ℂ] H)
    (dg dh A : ConnectionForm (B := B) (H := H)) :
    transformedForm h dh (transformedForm g dg A) =
      transformedForm (h.trans g) (productDerivative g h dg dh) A := by
  ext v w
  change h.symm (g.symm (A v (g (h w)) + dg v (h w)) + dh v w) =
    h.symm (g.symm (A v (g (h w)) + (g (dh v w) + dg v (h w))))
  simp only [map_add, ContinuousLinearEquiv.symm_apply_apply]
  abel

theorem transformedForm_identity (A : ConnectionForm (B := B) (H := H)) :
    transformedForm (ContinuousLinearEquiv.refl ℂ H) 0 A = A := by
  ext v w
  simp [transformedForm_apply]

/-- Apply the local law to the actual transition obtained from two Hermitian charts. -/
theorem hermitian_overlap_covariance
    {M : Type*} [TopologicalSpace M]
    {E : M → Type*} [∀ z, NormedAddCommGroup (E z)]
    [∀ z, InnerProductSpace ℂ (E z)] [TopologicalSpace (Bundle.TotalSpace H E)]
    (e f : Bundle.Trivialization H (Bundle.TotalSpace.proj (F := H) (E := E)))
    [e.IsLinear ℂ] [f.IsLinear ℂ]
    (he : HermitianFrames.IsHermitianChart e)
    (hf : HermitianFrames.IsHermitianChart f)
    (φ : B → M) (x : B) (hx : φ x ∈ e.baseSet) (hy : φ x ∈ f.baseSet)
    (dG : ConnectionForm (B := B) (H := H))
    (hG : HasFDerivAt (fun y => HermitianFrames.overlapOperator e f (φ y)) dG x)
    {u : B → H} {du : B →L[ℝ] H} (hu : HasFDerivAt u du x)
    (A : ConnectionForm (B := B) (H := H)) (v : B) :
    let g := (HermitianFrames.transition e f he hf (φ x) hx hy).toContinuousLinearEquiv
    covariantAt (transformedForm g dG A) u x v =
      g.symm (covariantAt A
        (fun y => HermitianFrames.overlapOperator e f (φ y) (u y)) x v) := by
  apply covariantAt_transformed _ hG _ hu A v
  exact HermitianFrames.overlapOperator_eq_transition e f he hf (φ x) hx hy

end GeneratedFoundations.Geometry.SourceFrameConnection
