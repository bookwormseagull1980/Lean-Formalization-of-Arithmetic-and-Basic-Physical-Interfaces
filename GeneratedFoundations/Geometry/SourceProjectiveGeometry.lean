module

public import GeneratedFoundations.Geometry.SourceQuaternionAmplitude
public import GeneratedFoundations.Geometry.SourceObservationSpectrum
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Projective geometry of the complete central observations

The target is the projectivization of an independent four-dimensional real
Euclidean space. Its topology is the quotient topology of nonzero vectors by
nonzero real scaling. Normalization proves that the sphere projection is a
quotient map whose fibres are precisely antipodal pairs. The actual source
group therefore induces a homeomorphism from its central quotient to this
projective space. The character space of all central-invariant observations
has the same identification.
-/

@[expose] public section

noncomputable section

open Topology
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceObservationSpectrum

namespace GeneratedFoundations.Geometry.SourceProjectiveGeometry

abbrev ResponseVector := EuclideanSpace ℝ (Fin 4)
abbrev NonzeroVector := {v : ResponseVector // v ≠ 0}
abbrev RP3 := Projectivization ℝ ResponseVector

/-- The topology is defined from nonzero Euclidean vectors, independently of
the source group and its observations. -/
instance projectiveTopology : TopologicalSpace RP3 :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℝ ResponseVector)))

def nonzeroProjection : C(NonzeroVector, RP3) :=
  ⟨Projectivization.mk' ℝ, continuous_quotient_mk'⟩

theorem nonzeroProjection_isQuotientMap : IsQuotientMap nonzeroProjection :=
  isQuotientMap_quotient_mk'

theorem sphere_norm (x : Sphere3) : ‖(x : ResponseVector)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.property

theorem sphere_nonzero (x : Sphere3) : (x : ResponseVector) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [sphere_norm]
  exact one_ne_zero

def sphereNonzero : C(Sphere3, NonzeroVector) where
  toFun x := ⟨x, sphere_nonzero x⟩
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val

def sphereProjection : C(Sphere3, RP3) := nonzeroProjection.comp sphereNonzero

@[simp] theorem sphereProjection_apply (x : Sphere3) :
    sphereProjection x = Projectivization.mk ℝ (x : ResponseVector) (sphere_nonzero x) := rfl

def normalizedSphere : C(NonzeroVector, Sphere3) where
  toFun v := ⟨NormedSpace.normalize (v : ResponseVector),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize v.property)⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun v : NonzeroVector => ‖(v : ResponseVector)‖⁻¹ • (v : ResponseVector))
    exact (continuous_subtype_val.norm.inv₀
      (fun v : NonzeroVector => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val

theorem normalizedSphere_sphereNonzero (x : Sphere3) :
    normalizedSphere (sphereNonzero x) = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (sphere_norm x)

theorem sphereProjection_normalized (v : NonzeroVector) :
    sphereProjection (normalizedSphere v) = nonzeroProjection v := by
  change Projectivization.mk ℝ (NormedSpace.normalize (v : ResponseVector)) _ =
    Projectivization.mk ℝ (v : ResponseVector) v.property
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  exact ⟨‖(v : ResponseVector)‖⁻¹, rfl⟩

/-- The sphere carries the usual projective quotient, not a transported topology. -/
theorem sphereProjection_isQuotientMap : IsQuotientMap sphereProjection := by
  have hcomp : sphereProjection ∘ normalizedSphere = nonzeroProjection := by
    funext v
    exact sphereProjection_normalized v
  apply IsQuotientMap.of_comp normalizedSphere.continuous sphereProjection.continuous
  rw [hcomp]
  exact nonzeroProjection_isQuotientMap

theorem sphereProjection_eq_iff (x y : Sphere3) :
    sphereProjection x = sphereProjection y ↔
      (x : ResponseVector) = (y : ResponseVector) ∨
      (x : ResponseVector) = -(y : ResponseVector) := by
  rw [sphereProjection_apply, sphereProjection_apply, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨r, hr⟩
    have hnorm : |r| = 1 := by
      have h := congrArg norm hr
      simpa only [norm_smul, Real.norm_eq_abs, sphere_norm, mul_one] using h
    rcases le_total 0 r with hp | hn
    · have h1 : r = 1 := by simpa only [abs_of_nonneg hp] using hnorm
      exact Or.inl (by simpa only [h1, one_smul] using hr.symm)
    · have hm : r = -1 := by
        rw [abs_of_nonpos hn] at hnorm
        linarith
      exact Or.inr (by simpa only [hm, neg_one_smul] using hr.symm)
  · rintro (h | h)
    · exact ⟨1, by simpa only [one_smul] using h.symm⟩
    · exact ⟨-1, by simpa only [neg_one_smul] using h.symm⟩

def sourceProjection : C(SU2, RP3) :=
  sphereProjection.comp ⟨sourceSphereHomeomorph, sourceSphereHomeomorph.continuous⟩

@[simp] theorem sourceProjection_apply (U : SU2) :
    sourceProjection U = sphereProjection (sourceSphereHomeomorph U) := rfl

theorem sourceProjection_isQuotientMap : IsQuotientMap sourceProjection :=
  sphereProjection_isQuotientMap.comp sourceSphereHomeomorph.isQuotientMap

/-- No source operations other than the two central translates are identified. -/
theorem sourceProjection_eq_iff (U V : SU2) :
    sourceProjection U = sourceProjection V ↔ U = V ∨ U = negativeIdentity * V := by
  rw [sourceProjection_apply, sourceProjection_apply, sphereProjection_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (sourceSphereHomeomorph.injective (Subtype.ext h))
    · right
      apply sourceSphereHomeomorph.injective
      apply Subtype.ext
      rw [sourceSphere_central]
      exact h
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (sourceSphere_central V)

theorem sourceProjection_eq_iff_quotient (U V : SU2) :
    sourceProjection U = sourceProjection V ↔ quotientContinuous U = quotientContinuous V := by
  rw [sourceProjection_eq_iff]
  exact (quotientMap_eq_iff U V).symm

def projectiveDescend : C(CentralQuotient, RP3) :=
  quotientContinuous_isQuotientMap.lift sourceProjection
    (fun {U V} h => (sourceProjection_eq_iff_quotient U V).mpr h)

@[simp] theorem projectiveDescend_apply (U : SU2) :
    projectiveDescend (quotientContinuous U) = sourceProjection U :=
  congrArg (fun f : C(SU2, RP3) => f U)
    (quotientContinuous_isQuotientMap.lift_comp sourceProjection
      (fun {U V} h => (sourceProjection_eq_iff_quotient U V).mpr h))

def projectiveAscend : C(RP3, CentralQuotient) :=
  sourceProjection_isQuotientMap.lift quotientContinuous
    (fun {U V} h => (sourceProjection_eq_iff_quotient U V).mp h)

@[simp] theorem projectiveAscend_apply (U : SU2) :
    projectiveAscend (sourceProjection U) = quotientContinuous U :=
  congrArg (fun f : C(SU2, CentralQuotient) => f U)
    (sourceProjection_isQuotientMap.lift_comp quotientContinuous
      (fun {U V} h => (sourceProjection_eq_iff_quotient U V).mp h))

/-- The actual central quotient is homeomorphic to independent real projective 3-space. -/
def centralProjectiveHomeomorph : CentralQuotient ≃ₜ RP3 where
  toFun := projectiveDescend
  invFun := projectiveAscend
  left_inv q := by
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    rw [projectiveDescend_apply, projectiveAscend_apply]
  right_inv p := by
    obtain ⟨U, rfl⟩ := sourceProjection_isQuotientMap.surjective p
    rw [projectiveAscend_apply, projectiveDescend_apply]
  continuous_toFun := projectiveDescend.continuous
  continuous_invFun := projectiveAscend.continuous

@[simp] theorem centralProjectiveHomeomorph_apply (U : SU2) :
    centralProjectiveHomeomorph (quotientContinuous U) =
      Projectivization.mk ℝ (sourceSphereHomeomorph U : ResponseVector)
        (sphere_nonzero (sourceSphereHomeomorph U)) :=
  projectiveDescend_apply U

/-- Compatibility with the original source projection fixes the identification. -/
theorem centralProjectiveHomeomorph_unique (e : CentralQuotient ≃ₜ RP3)
    (he : ∀ U : SU2, e (quotientContinuous U) = sourceProjection U) :
    e = centralProjectiveHomeomorph := by
  apply Homeomorph.ext
  intro q
  obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
  exact (he U).trans (projectiveDescend_apply U).symm

instance projective_compact : CompactSpace RP3 := centralProjectiveHomeomorph.compactSpace

instance projective_hausdorff : T2Space RP3 := centralProjectiveHomeomorph.t2Space

/-- Every continuous invariant source observation has its full projective readout. -/
def projectiveStarAlgEquiv : invariantAlgebra ≃⋆ₐ[ℂ] C(RP3, ℂ) :=
  descentStarAlgEquiv.trans
    (Homeomorph.compStarAlgEquiv' ℂ ℂ centralProjectiveHomeomorph.symm)

@[simp] theorem projectiveStarAlgEquiv_apply (f : invariantAlgebra) (U : SU2) :
    projectiveStarAlgEquiv f (sourceProjection U) = f.val U := by
  change descentStarAlgEquiv f
    (centralProjectiveHomeomorph.symm (sourceProjection U)) = f.val U
  have h : centralProjectiveHomeomorph.symm (sourceProjection U) = quotientContinuous U := by
    rw [← projectiveDescend_apply]
    exact centralProjectiveHomeomorph.symm_apply_apply _
  rw [h]
  exact descend_apply f.val f.property U

@[simp] theorem projectiveStarAlgEquiv_symm_apply (g : C(RP3, ℂ)) (U : SU2) :
    (projectiveStarAlgEquiv.symm g).val U = g (sourceProjection U) := by
  have h := projectiveStarAlgEquiv_apply (projectiveStarAlgEquiv.symm g) U
  rw [StarAlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem projectiveStarAlgEquiv_norm (f : invariantAlgebra) :
    ‖projectiveStarAlgEquiv f‖ = ‖f.val‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro p
    obtain ⟨U, rfl⟩ := sourceProjection_isQuotientMap.surjective p
    rw [projectiveStarAlgEquiv_apply]
    exact f.val.norm_coe_le_norm U
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro U
    rw [← projectiveStarAlgEquiv_apply f U]
    exact (projectiveStarAlgEquiv f).norm_coe_le_norm (sourceProjection U)

theorem projective_readout_unique (f : invariantAlgebra) (g : C(RP3, ℂ))
    (hg : ∀ U : SU2, g (sourceProjection U) = f.val U) :
    g = projectiveStarAlgEquiv f := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨U, rfl⟩ := sourceProjection_isQuotientMap.surjective p
  rw [projectiveStarAlgEquiv_apply]
  exact hg U

/-- All characters of the invariant algebra are included in this identification. -/
def characterProjectiveHomeomorph :
    WeakDual.characterSpace ℂ invariantAlgebra ≃ₜ RP3 :=
  quotientCharacterHomeomorph.symm.trans centralProjectiveHomeomorph

@[simp] theorem characterProjectiveHomeomorph_source (U : SU2) :
    characterProjectiveHomeomorph (sourceCharacter U) = sourceProjection U := by
  change centralProjectiveHomeomorph
    (quotientCharacterHomeomorph.symm
      (quotientCharacterHomeomorph (quotientContinuous U))) = sourceProjection U
  rw [Homeomorph.symm_apply_apply]
  exact projectiveDescend_apply U

theorem observations_equal_iff_projective (U V : SU2) :
    (∀ f : invariantAlgebra, f.val U = f.val V) ↔ sourceProjection U = sourceProjection V := by
  rw [observations_equal_iff]
  exact (sourceProjection_eq_iff_quotient U V).symm

end GeneratedFoundations.Geometry.SourceProjectiveGeometry
