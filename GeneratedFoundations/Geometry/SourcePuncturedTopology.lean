module

public import GeneratedFoundations.Geometry.SourceLeftRightAction
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Product

/-!
# Punctured charts of the generated source

Removing any point from the actual source group gives a contractible space.
The chart is the stereographic projection of the previously constructed
source sphere, with its ordinary subspace topology. Its target is the real
orthogonal complement of the omitted unit vector.

Loops whose images avoid a source point are therefore null-homotopic. This
statement does not assert that every continuous loop avoids a point. The
passage from arbitrary loops to suitable representatives is a separate
global assertion.
-/

@[expose] public section

noncomputable section

open Topology Set
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceProjectiveGeometry (ResponseVector sphere_norm)
open GeneratedFoundations.Geometry.SourceLeftRightAction (SourcePair)

namespace GeneratedFoundations.Geometry.SourcePuncturedTopology

abbrev PuncturedSphere (p : Sphere3) := {x : Sphere3 // x ≠ p}
abbrev PuncturedSource (p : SU2) := {x : SU2 // x ≠ p}

/-- The usual stereographic chart on the independent Euclidean sphere. -/
def spherePunctureHomeomorph (p : Sphere3) :
    PuncturedSphere p ≃ₜ (ℝ ∙ (p : ResponseVector))ᗮ where
  toFun x := stereoToFun (p : ResponseVector) (x : Sphere3)
  invFun w := ⟨stereoInvFun (sphere_norm p) w, by
    simpa only [Subtype.eta] using stereoInvFun_ne_north_pole (sphere_norm p) w⟩
  left_inv x := by
    apply Subtype.ext
    exact stereo_left_inv (sphere_norm p) (fun h => x.property (Subtype.ext h))
  right_inv w := stereo_right_inv (sphere_norm p) w
  continuous_toFun := by
    change Continuous ((stereographic (sphere_norm p)).source.domRestrict
      (stereographic (sphere_norm p)))
    exact (stereographic (sphere_norm p)).continuousOn.domRestrict
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_stereoInvFun (sphere_norm p)

/-- Restriction of the same source homeomorphism; no new topology is assigned. -/
def sourcePunctureSphereHomeomorph (p : SU2) :
    PuncturedSource p ≃ₜ PuncturedSphere (sourceSphereHomeomorph p) :=
  sourceSphereHomeomorph.subtype (fun x => by
    exact not_congr sourceSphereHomeomorph.injective.eq_iff.symm)

def sourcePunctureHomeomorph (p : SU2) :
    PuncturedSource p ≃ₜ
      (ℝ ∙ (sourceSphereHomeomorph p : ResponseVector))ᗮ :=
  (sourcePunctureSphereHomeomorph p).trans
    (spherePunctureHomeomorph (sourceSphereHomeomorph p))

theorem punctured_sphere_contractible (p : Sphere3) :
    ContractibleSpace (PuncturedSphere p) :=
  (spherePunctureHomeomorph p).contractibleSpace

theorem punctured_source_contractible (p : SU2) :
    ContractibleSpace (PuncturedSource p) :=
  (sourcePunctureHomeomorph p).contractibleSpace

theorem punctured_source_simplyConnected (p : SU2) :
    SimplyConnectedSpace (PuncturedSource p) := by
  let : ContractibleSpace (PuncturedSource p) := punctured_source_contractible p
  infer_instance

/-- Two paths can be contracted relative to their common endpoints whenever
they lie in the same punctured chart. -/
theorem paths_homotopic_of_punctured_contractible {X : Type*} [TopologicalSpace X]
    (p : X) (hc : ContractibleSpace {x : X // x ≠ p}) {x y : X}
    (γ δ : Path x y) (hγ : ∀ t, γ t ≠ p) (hδ : ∀ t, δ t ≠ p) :
    Path.Homotopic γ δ := by
  let : ContractibleSpace {x : X // x ≠ p} := hc
  have hx : x ≠ p := by simpa using hγ 0
  have hy : y ≠ p := by simpa using hγ 1
  let γ' : Path (⟨x, hx⟩ : {x : X // x ≠ p}) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := continuous_induced_rng.mpr γ.continuous
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  let δ' : Path (⟨x, hx⟩ : {x : X // x ≠ p}) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨δ t, hδ t⟩
      continuous_toFun := continuous_induced_rng.mpr δ.continuous
      source' := Subtype.ext δ.source
      target' := Subtype.ext δ.target }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic γ' δ'
  refine ⟨(F.map ⟨Subtype.val, continuous_subtype_val⟩).cast ?_ ?_⟩
  · apply Path.ext
    funext t
    rfl
  · apply Path.ext
    funext t
    rfl

theorem source_paths_homotopic_of_avoid (p : SU2) {x y : SU2}
    (γ δ : Path x y) (hγ : ∀ t, γ t ≠ p) (hδ : ∀ t, δ t ≠ p) :
    Path.Homotopic γ δ :=
  paths_homotopic_of_punctured_contractible p
    (punctured_source_contractible p) γ δ hγ hδ

theorem sphere_paths_homotopic_of_avoid (p : Sphere3) {x y : Sphere3}
    (γ δ : Path x y) (hγ : ∀ t, γ t ≠ p) (hδ : ∀ t, δ t ≠ p) :
    Path.Homotopic γ δ :=
  paths_homotopic_of_punctured_contractible p
    (punctured_sphere_contractible p) γ δ hγ hδ

theorem sphere_loop_nullhomotopic_of_avoid (p : Sphere3) {x : Sphere3}
    (γ : Path x x) (hγ : ∀ t, γ t ≠ p) :
    Path.Homotopic γ (Path.refl x) := by
  apply sphere_paths_homotopic_of_avoid p γ (Path.refl x) hγ
  intro t
  simpa using hγ 0

theorem source_loop_nullhomotopic_of_avoid (p : SU2) {x : SU2}
    (γ : Path x x) (hγ : ∀ t, γ t ≠ p) :
    Path.Homotopic γ (Path.refl x) := by
  apply source_paths_homotopic_of_avoid p γ (Path.refl x) hγ
  intro t
  simpa using hγ 0

/-- Path connectedness is unconditional and follows from the full sphere. -/
theorem source_pathConnected : PathConnectedSpace SU2 := by
  have hrank : 1 < Module.rank ℝ ResponseVector := by
    rw [← Module.finrank_eq_rank ℝ ResponseVector, finrank_euclideanSpace_fin]
    norm_num
  let : PathConnectedSpace Sphere3 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere hrank (0 : ResponseVector) (r := 1) (by norm_num))
  exact sourceSphereHomeomorph.symm.pathConnectedSpace

theorem sourcePair_pathConnected : PathConnectedSpace SourcePair := by
  let : PathConnectedSpace SU2 := source_pathConnected
  infer_instance

/-- The product assertion follows by taking the actual coordinate homotopies. -/
theorem simplyConnected_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace (X × Y) := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance, ?_⟩
  intro x y γ δ
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic
    (γ.map continuous_fst) (δ.map continuous_fst)
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic
    (γ.map continuous_snd) (δ.map continuous_snd)
  refine ⟨(Path.Homotopic.prodHomotopy F G).cast ?_ ?_⟩
  · apply Path.ext
    funext t
    exact Prod.eta _
  · apply Path.ext
    funext t
    exact Prod.eta _

/-- Both local factors are genuine punctured domains of the two source groups. -/
theorem punctured_sourcePair_contractible (p q : SU2) :
    ContractibleSpace (PuncturedSource p × PuncturedSource q) := by
  let : ContractibleSpace (PuncturedSource p) := punctured_source_contractible p
  let : ContractibleSpace (PuncturedSource q) := punctured_source_contractible q
  infer_instance

/-- Transport of simple connectedness does not replace its sphere proof. -/
theorem source_simplyConnected_iff_sphere :
    SimplyConnectedSpace SU2 ↔ SimplyConnectedSpace Sphere3 :=
  sourceSphereHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff

theorem sourcePair_simplyConnected_of_source (h : SimplyConnectedSpace SU2) :
    SimplyConnectedSpace SourcePair := by
  let : SimplyConnectedSpace SU2 := h
  exact simplyConnected_prod

end GeneratedFoundations.Geometry.SourcePuncturedTopology
