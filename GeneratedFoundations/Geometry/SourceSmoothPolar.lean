module

public import GeneratedFoundations.Geometry.SourceSphereTangent
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Smooth polar coordinates of the generated real amplitude

Positive radii and nonzero quaternion amplitudes carry the open-submanifold
structures inherited from their ambient vector spaces. The angular factor
is the same independent Euclidean sphere as in `SourceSphereTangent`, with
its stereographic analytic atlas. Radial multiplication and the explicit
inverse given by norm and normalization form a smooth diffeomorphism.

The derivative is calculated from the actual inclusion of that sphere and
scalar multiplication. In the product tangent coordinates it is exactly
the previously constructed `polarTangentMap`. Thus the source trace polar
formula is a pullback by the derivative of the actual polar map. No
connection or curvature assertion is made here.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Quaternion RealInnerProductSpace Manifold ContDiff
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceSphereTangent

namespace GeneratedFoundations.Geometry.SourceSmoothPolar

local instance : Fact (Module.finrank ℝ Ambient = 3 + 1) :=
  ⟨by simp [Ambient]⟩

def positiveRay : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
def puncturedAmplitude : TopologicalSpace.Opens ℍ := ⟨{h | h ≠ 0}, isOpen_ne⟩

abbrev Radius := positiveRay
abbrev NonzeroAmplitude := puncturedAmplitude
abbrev PolarCarrier := Radius × Sphere3
abbrev polarModel := (𝓘(ℝ, ℝ)).prod (𝓡 3)

/-- Radial multiplication on the full real-radius product, before restriction. -/
def amplitude (p : ℝ × Sphere3) : ℍ := p.1 • quaternionPoint p.2

theorem quaternionPoint_contMDiff :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℍ) ∞ quaternionPoint :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap.contMDiff.comp
    contMDiff_coe_sphere

theorem amplitude_contMDiff : ContMDiff polarModel 𝓘(ℝ, ℍ) ∞ amplitude :=
  contMDiff_fst.smul (quaternionPoint_contMDiff.comp contMDiff_snd)

theorem amplitude_norm {r : ℝ} (hr : 0 < r) (q : Sphere3) :
    ‖amplitude (r, q)‖ = r := by
  rw [amplitude, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    quaternionPoint_norm, mul_one]

theorem amplitude_ne_zero {r : ℝ} (hr : 0 < r) (q : Sphere3) :
    amplitude (r, q) ≠ 0 := by
  apply norm_pos_iff.mp
  rw [amplitude_norm hr]
  exact hr

def polar (p : PolarCarrier) : NonzeroAmplitude :=
  ⟨amplitude ((p.1 : ℝ), p.2), amplitude_ne_zero p.1.property p.2⟩

@[simp] theorem polar_coe (p : PolarCarrier) :
    (polar p : ℍ) = (p.1 : ℝ) • quaternionPoint p.2 := rfl

def normalizedSphere (h : NonzeroAmplitude) : Sphere3 :=
  ⟨Quaternion.linearIsometryEquivTuple (NormedSpace.normalize (h : ℍ)), by
    rw [Metric.mem_sphere, dist_zero_right,
      Quaternion.linearIsometryEquivTuple.norm_map]
    exact NormedSpace.norm_normalize h.property⟩

@[simp] theorem normalizedSphere_coe (h : NonzeroAmplitude) :
    (normalizedSphere h : Ambient) =
      Quaternion.linearIsometryEquivTuple (NormedSpace.normalize (h : ℍ)) := rfl

theorem quaternionPoint_normalizedSphere (h : NonzeroAmplitude) :
    quaternionPoint (normalizedSphere h) = NormedSpace.normalize (h : ℍ) :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply _

def polarInverse (h : NonzeroAmplitude) : PolarCarrier :=
  (⟨‖(h : ℍ)‖, norm_pos_iff.mpr h.property⟩, normalizedSphere h)

@[simp] theorem polarInverse_radius (h : NonzeroAmplitude) :
    ((polarInverse h).1 : ℝ) = ‖(h : ℍ)‖ := rfl

theorem polarInverse_polar (p : PolarCarrier) : polarInverse (polar p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact amplitude_norm p.1.property p.2
  · apply Subtype.ext
    change Quaternion.linearIsometryEquivTuple
      (NormedSpace.normalize ((p.1 : ℝ) • quaternionPoint p.2)) = (p.2 : Ambient)
    rw [NormedSpace.normalize_smul_of_pos p.1.property,
      NormedSpace.normalize_eq_self_of_norm_eq_one (quaternionPoint_norm p.2)]
    exact Quaternion.linearIsometryEquivTuple.apply_symm_apply p.2

theorem polar_polarInverse (h : NonzeroAmplitude) : polar (polarInverse h) = h := by
  apply Subtype.ext
  change ‖(h : ℍ)‖ • quaternionPoint (normalizedSphere h) = (h : ℍ)
  rw [quaternionPoint_normalizedSphere, NormedSpace.norm_smul_normalize]

def polarEquiv : PolarCarrier ≃ NonzeroAmplitude where
  toFun := polar
  invFun := polarInverse
  left_inv := polarInverse_polar
  right_inv := polar_polarInverse

theorem radiusValue_contMDiff :
    ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, ℝ) ∞ (fun h : NonzeroAmplitude => ‖(h : ℍ)‖) := by
  intro h
  exact (contDiffAt_norm ℝ h.property).comp_contMDiffAt
    (contMDiff_subtype_val.contMDiffAt)

theorem normalizedAmplitude_contMDiff :
    ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞
      (fun h : NonzeroAmplitude => NormedSpace.normalize (h : ℍ)) := by
  have hn : ∀ h : NonzeroAmplitude, ‖(h : ℍ)‖ ≠ 0 :=
    fun h => norm_ne_zero_iff.mpr h.property
  exact (radiusValue_contMDiff.inv₀ hn).smul contMDiff_subtype_val

theorem normalizedSphere_contMDiff :
    ContMDiff 𝓘(ℝ, ℍ) (𝓡 3) ∞ normalizedSphere := by
  have hn : ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, Ambient) ∞
      (fun h : NonzeroAmplitude =>
        Quaternion.linearIsometryEquivTuple (NormedSpace.normalize (h : ℍ))) :=
    Quaternion.linearIsometryEquivTuple.toContinuousLinearMap.contMDiff.comp
      normalizedAmplitude_contMDiff
  exact hn.codRestrict_sphere (fun h => (normalizedSphere h).property)

theorem polar_contMDiff : ContMDiff polarModel 𝓘(ℝ, ℍ) ∞ polar := by
  apply (ContMDiff.subtypeVal_comp_iff puncturedAmplitude polar).mp
  have hr : ContMDiff polarModel 𝓘(ℝ, ℝ) ∞
      (fun p : PolarCarrier => (p.1 : ℝ)) :=
    contMDiff_subtype_val.comp contMDiff_fst
  exact hr.smul (quaternionPoint_contMDiff.comp contMDiff_snd)

theorem polarInverse_contMDiff : ContMDiff 𝓘(ℝ, ℍ) polarModel ∞ polarInverse := by
  have hr : ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, ℝ) ∞
      (fun h : NonzeroAmplitude => (polarInverse h).1) := by
    apply (ContMDiff.subtypeVal_comp_iff positiveRay _).mp
    exact radiusValue_contMDiff
  exact hr.prodMk normalizedSphere_contMDiff

/-- A diffeomorphism with the inherited open-submanifold and sphere structures. -/
def polarDiffeomorph : PolarCarrier ≃ₘ⟮polarModel, 𝓘(ℝ, ℍ)⟯ NonzeroAmplitude where
  toEquiv := polarEquiv
  contMDiff_toFun := polar_contMDiff
  contMDiff_invFun := polarInverse_contMDiff

/-- Canonical product tangent coordinates, with the normed-space tangent identification
only in the radial factor. The sphere tangent factor retains its original atlas. -/
def productTangentCoordinates (p : ℝ × Sphere3) :
    TangentSpace polarModel p ≃L[ℝ] (ℝ × SphereTangent p.2) :=
  (NormedSpace.fromTangentSpace p.1).prodCongr
    (ContinuousLinearEquiv.refl ℝ (SphereTangent p.2))

@[simp] theorem productTangentCoordinates_apply (p : ℝ × Sphere3)
    (v : TangentSpace polarModel p) : productTangentCoordinates p v = (v.1, v.2) := rfl

theorem quaternionPoint_mvfderiv (q : Sphere3) :
    mvfderiv (𝓡 3) quaternionPoint q = quaternionDerivative q := by
  let L := Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap
  change mvfderiv (𝓡 3) (L ∘ (Subtype.val : Sphere3 → Ambient)) q =
    L.comp (inclusionDerivative q)
  rw [mvfderiv_comp q L.differentiableAt.mdifferentiableAt
    (contMDiff_coe_sphere.mdifferentiableAt one_ne_zero),
    mvfderiv_eq_fderiv, L.fderiv]
  rfl

/-- Differentiating radial multiplication gives the already constructed polar linear map. -/
theorem amplitude_mvfderiv (p : ℝ × Sphere3) :
    mvfderiv polarModel amplitude p =
      (polarTangentMap p.2 p.1).comp (productTangentCoordinates p).toContinuousLinearMap := by
  have hq : MDifferentiableAt polarModel 𝓘(ℝ, ℍ)
      (quaternionPoint ∘ Prod.snd) p :=
    (quaternionPoint_contMDiff.comp contMDiff_snd).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt polarModel 𝓘(ℝ, ℝ) (@Prod.fst ℝ Sphere3) p :=
    mdifferentiableAt_fst
  have hqd : mvfderiv polarModel (quaternionPoint ∘ Prod.snd) p =
      (quaternionDerivative p.2).comp (ContinuousLinearMap.snd ℝ ℝ (SphereTangent p.2)) := by
    rw [mvfderiv_comp p (quaternionPoint_contMDiff.mdifferentiableAt (by simp))
      mdifferentiableAt_snd, quaternionPoint_mvfderiv, mfderiv_snd]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hfd : mvfderiv polarModel (@Prod.fst ℝ Sphere3) p =
      ContinuousLinearMap.fst ℝ ℝ (SphereTangent p.2) := by
    unfold mvfderiv
    rw [mfderiv_fst]
    rfl
  change mvfderiv polarModel ((@Prod.fst ℝ Sphere3) • (quaternionPoint ∘ Prod.snd)) p = _
  rw [mvfderiv_smul hf hq, hqd, hfd]
  apply ContinuousLinearMap.ext
  intro v
  change p.1 • quaternionDerivative p.2 v.2 + v.1 • quaternionPoint p.2 =
    v.1 • quaternionPoint p.2 + p.1 • quaternionDerivative p.2 v.2
  exact add_comm _ _

theorem amplitude_mfderiv (p : ℝ × Sphere3) :
    (NormedSpace.fromTangentSpace (amplitude p)).toContinuousLinearMap.comp
      (mfderiv polarModel 𝓘(ℝ, ℍ) amplitude p) =
      (polarTangentMap p.2 p.1).comp (productTangentCoordinates p).toContinuousLinearMap :=
  amplitude_mvfderiv p

/-- The canonical open chart on a positive radius has the ordinary unit derivative. -/
theorem radius_hasMFDerivAt (r : Radius) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : Radius → ℝ) r
      (ContinuousLinearMap.id ℝ ℝ) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have heq := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℝ) positiveRay (x := r)).symm
  change (fun t : ℝ => ((chartAt ℝ r).symm t : ℝ)) =ᶠ[𝓝 (r : ℝ)]
    (fun t : ℝ => t) at heq
  change HasFDerivWithinAt (fun t : ℝ => ((chartAt ℝ r).symm t : ℝ))
    (ContinuousLinearMap.id ℝ ℝ) (Set.range (id : ℝ → ℝ)) (r : ℝ)
  exact ((hasFDerivAt_id (r : ℝ)).congr_of_eventuallyEq heq).hasFDerivWithinAt

def positiveProductCoordinates (p : PolarCarrier) :
    TangentSpace polarModel p ≃L[ℝ] (ℝ × SphereTangent p.2) :=
  ContinuousLinearEquiv.refl ℝ _

@[simp] theorem positiveProductCoordinates_apply (p : PolarCarrier)
    (v : TangentSpace polarModel p) : positiveProductCoordinates p v = (v.1, v.2) := rfl

/-- The same derivative formula on the positive-radius domain of the diffeomorphism.
The first coordinate is justified by `radius_hasMFDerivAt`, not by an assigned velocity. -/
theorem polar_mvfderiv (p : PolarCarrier) :
    mvfderiv polarModel (fun z : PolarCarrier => (polar z : ℍ)) p =
      (polarTangentMap p.2 (p.1 : ℝ)).comp
        (positiveProductCoordinates p).toContinuousLinearMap := by
  have hr : MDifferentiableAt polarModel 𝓘(ℝ, ℝ)
      (fun z : PolarCarrier => (z.1 : ℝ)) p :=
    ((contMDiff_subtype_val (n := ∞)).comp contMDiff_fst).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt polarModel 𝓘(ℝ, ℍ)
      (quaternionPoint ∘ Prod.snd) p :=
    (quaternionPoint_contMDiff.comp contMDiff_snd).mdifferentiableAt (by simp)
  have hrd : mvfderiv polarModel (fun z : PolarCarrier => (z.1 : ℝ)) p =
      ContinuousLinearMap.fst ℝ ℝ (SphereTangent p.2) := by
    change mvfderiv polarModel ((Subtype.val : Radius → ℝ) ∘ Prod.fst) p = _
    rw [mvfderiv_comp p (radius_hasMFDerivAt p.1).mdifferentiableAt
      mdifferentiableAt_fst]
    have hd : mvfderiv 𝓘(ℝ, ℝ) (Subtype.val : Radius → ℝ) p.1 =
        ContinuousLinearMap.id ℝ ℝ := by
      unfold mvfderiv
      rw [(radius_hasMFDerivAt p.1).mfderiv]
      rfl
    rw [hd, mfderiv_fst]
    rfl
  have hqd : mvfderiv polarModel (quaternionPoint ∘ Prod.snd) p =
      (quaternionDerivative p.2).comp (ContinuousLinearMap.snd ℝ ℝ (SphereTangent p.2)) := by
    rw [mvfderiv_comp p (quaternionPoint_contMDiff.mdifferentiableAt (by simp))
      mdifferentiableAt_snd, quaternionPoint_mvfderiv, mfderiv_snd]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  change mvfderiv polarModel
    ((fun z : PolarCarrier => (z.1 : ℝ)) • (quaternionPoint ∘ Prod.snd)) p = _
  rw [mvfderiv_smul hr hq, hrd, hqd]
  apply ContinuousLinearMap.ext
  intro v
  change (p.1 : ℝ) • quaternionDerivative p.2 v.2 + v.1 • quaternionPoint p.2 =
    v.1 • quaternionPoint p.2 + (p.1 : ℝ) • quaternionDerivative p.2 v.2
  exact add_comm _ _

theorem polar_mfderiv (p : PolarCarrier) :
    (NormedSpace.fromTangentSpace (polar p : ℍ)).toContinuousLinearMap.comp
      (mfderiv polarModel 𝓘(ℝ, ℍ) (fun z : PolarCarrier => (polar z : ℍ)) p) =
      (polarTangentMap p.2 (p.1 : ℝ)).comp
        (positiveProductCoordinates p).toContinuousLinearMap :=
  polar_mvfderiv p

/-- The nonzero-amplitude inclusion has the identity derivative in its inherited open chart. -/
theorem amplitudeInclusion_hasMFDerivAt (h : NonzeroAmplitude) :
    HasMFDerivAt 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) (Subtype.val : NonzeroAmplitude → ℍ) h
      (ContinuousLinearMap.id ℝ ℍ) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have heq := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℍ) puncturedAmplitude (x := h)).symm
  change (fun z : ℍ => ((chartAt ℍ h).symm z : ℍ)) =ᶠ[𝓝 (h : ℍ)]
    (fun z : ℍ => z) at heq
  change HasFDerivWithinAt (fun z : ℍ => ((chartAt ℍ h).symm z : ℍ))
    (ContinuousLinearMap.id ℝ ℍ) (Set.range (id : ℍ → ℍ)) (h : ℍ)
  exact ((hasFDerivAt_id (h : ℍ)).congr_of_eventuallyEq heq).hasFDerivWithinAt

/-- The derivative of the diffeomorphism itself, with its nonzero open codomain.
The target tangent space is the inherited quaternion model, so the same linear map applies. -/
theorem polar_open_mfderiv (p : PolarCarrier) :
    mfderiv polarModel 𝓘(ℝ, ℍ) polar p =
      (polarTangentMap p.2 (p.1 : ℝ)).comp
        (positiveProductCoordinates p).toContinuousLinearMap := by
  have hd : mvfderiv 𝓘(ℝ, ℍ) (Subtype.val : NonzeroAmplitude → ℍ) (polar p) =
      ContinuousLinearMap.id ℝ ℍ := by
    unfold mvfderiv
    rw [(amplitudeInclusion_hasMFDerivAt (polar p)).mfderiv]
    rfl
  have hc := mvfderiv_comp p
    (amplitudeInclusion_hasMFDerivAt (polar p)).mdifferentiableAt
    (polar_contMDiff.mdifferentiableAt (by simp))
  have he : mfderiv polarModel 𝓘(ℝ, ℍ) polar p =
      mvfderiv polarModel (fun z : PolarCarrier => (polar z : ℍ)) p := by
    simpa only [hd, ContinuousLinearMap.id_comp, Function.comp_def] using! hc.symm
  exact he.trans (polar_mvfderiv p)

/-- The prepared source trace is the metric pullback along the genuine smooth polar map. -/
theorem polar_trace_pullback (p : PolarCarrier)
    (v w : TangentSpace polarModel p) :
    (Matrix.trace ((matrixMap
      (mvfderiv polarModel (fun z : PolarCarrier => (polar z : ℍ)) p v)).conjTranspose *
      matrixMap (mvfderiv polarModel (fun z : PolarCarrier => (polar z : ℍ)) p w))).re / 2 =
      v.1 * w.1 + (p.1 : ℝ) ^ 2 * sphereMetric p.2 v.2 w.2 := by
  simp only [polar_mvfderiv, ContinuousLinearMap.comp_apply]
  exact source_trace_polar_tangent p.2 (p.1 : ℝ) (v.1, v.2) (w.1, w.2)

end GeneratedFoundations.Geometry.SourceSmoothPolar
