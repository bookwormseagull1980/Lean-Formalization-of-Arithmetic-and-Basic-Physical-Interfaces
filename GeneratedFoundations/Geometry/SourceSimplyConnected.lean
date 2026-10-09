module

public import GeneratedFoundations.Geometry.SourcePuncturedTopology
public import Mathlib.Topology.Subpath
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Simple connectedness of the actual source group

An arbitrary continuous loop is subdivided into finitely many stereographic
charts. Within each chart it is homotopic, relative to its endpoints, to the
inverse image of a straight segment. Each replacement lies in the span of
the chart pole and its two endpoints. These are proper subspaces of the
four-dimensional amplitude space. A finite union of them omits a unit
vector, so the concatenated replacement contracts in a punctured sphere.

The source group and its left-right product inherit this result through the
previously established source homeomorphism. No non-surjectivity assumption
is made about the original loop.
-/

@[expose] public section

noncomputable section

open Topology Set
open scoped unitInterval
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceProjectiveGeometry (ResponseVector sphere_norm)
open GeneratedFoundations.Geometry.SourceLeftRightAction (SourcePair)
open GeneratedFoundations.Geometry.SourcePuncturedTopology

namespace GeneratedFoundations.Geometry.SourceSimplyConnected

def chartPath (p : Sphere3) (x y : PuncturedSphere p) :
    Path (x : Sphere3) (y : Sphere3) :=
  (((Path.segment (spherePunctureHomeomorph p x) (spherePunctureHomeomorph p y)).map
    (spherePunctureHomeomorph p).symm.continuous).cast
      ((spherePunctureHomeomorph p).symm_apply_apply x).symm
      ((spherePunctureHomeomorph p).symm_apply_apply y).symm).map
    continuous_subtype_val

theorem chartPath_avoids (p : Sphere3) (x y : PuncturedSphere p) (t : I) :
    chartPath p x y t ≠ p :=
  ((spherePunctureHomeomorph p).symm
    (Path.segment (spherePunctureHomeomorph p x) (spherePunctureHomeomorph p y) t)).property

def chartSpan (p x y : Sphere3) : Submodule ℝ ResponseVector :=
  Submodule.span ℝ (Set.range ![(p : ResponseVector), (x : ResponseVector),
    (y : ResponseVector)])

theorem chartSpan_ne_top (p x y : Sphere3) : chartSpan p x y ≠ ⊤ := by
  intro h
  have hc := finrank_le_of_span_eq_top (R := ℝ)
    (v := ![(p : ResponseVector), (x : ResponseVector), (y : ResponseVector)]) h
  norm_num [ResponseVector, finrank_euclideanSpace_fin] at hc

private theorem stereo_mem (p : Sphere3) (S : Submodule ℝ ResponseVector)
    (hp : (p : ResponseVector) ∈ S) {x : ResponseVector} (hx : x ∈ S) :
    (stereoToFun (p : ResponseVector) x : ResponseVector) ∈ S := by
  have hproj : (((ℝ ∙ (p : ResponseVector))ᗮ).orthogonalProjectionOnto x :
      ResponseVector) = x - (ℝ ∙ (p : ResponseVector)).starProjection x := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Submodule.starProjection_apply, add_comm] using
      (ℝ ∙ (p : ResponseVector)).starProjection_add_starProjection_orthogonal x
  have hline : (ℝ ∙ (p : ResponseVector)).starProjection x ∈ S := by
    rw [Submodule.starProjection_unit_singleton ℝ (sphere_norm p)]
    exact S.smul_mem _ hp
  change (2 / (1 - innerSL ℝ (p : ResponseVector) x)) •
    (((ℝ ∙ (p : ResponseVector))ᗮ).orthogonalProjectionOnto x : ResponseVector) ∈ S
  apply S.smul_mem
  rw [hproj]
  exact S.sub_mem hx hline

theorem chartPath_mem_span (p : Sphere3) (x y : PuncturedSphere p) (t : I) :
    (chartPath p x y t : ResponseVector) ∈ chartSpan p x y := by
  let S := chartSpan p x y
  have hp : (p : ResponseVector) ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have hx : ((x : Sphere3) : ResponseVector) ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have hy : ((y : Sphere3) : ResponseVector) ∈ S := Submodule.subset_span ⟨2, rfl⟩
  let w := Path.segment (spherePunctureHomeomorph p x) (spherePunctureHomeomorph p y) t
  have hw : (w : ResponseVector) ∈ S := by
    change (AffineMap.lineMap (spherePunctureHomeomorph p x)
      (spherePunctureHomeomorph p y) (t : ℝ) : ResponseVector) ∈ S
    rw [AffineMap.lineMap_apply_module]
    exact S.add_mem (S.smul_mem _ (stereo_mem p S hp hx))
      (S.smul_mem _ (stereo_mem p S hp hy))
  change (stereoInvFun (sphere_norm p) w : ResponseVector) ∈ S
  exact S.smul_mem _ (S.add_mem (S.smul_mem _ hw) (S.smul_mem _ hp))

/-- Finite unions of proper amplitude subspaces cannot cover the source sphere. -/
theorem exists_sphere_point_outside {ι : Type*} [Finite ι] [Nonempty ι]
    (S : ι → Submodule ℝ ResponseVector) (hS : ∀ i, S i ≠ ⊤) :
    ∃ p : Sphere3, ∀ i, (p : ResponseVector) ∉ S i := by
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top S hS
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact hv i (by simpa only [h] using (S i).zero_mem)
  let p : Sphere3 := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere_zero_iff_norm, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]⟩
  refine ⟨p, fun i hi => hv i ?_⟩
  exact ((S i).smul_mem_iff (inv_ne_zero (norm_ne_zero_iff.mpr hv0))).mp hi

private theorem concat_range_subset {X : Type*} [TopologicalSpace X] {n : ℕ}
    (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (s : Set X) (hp : p 0 ∈ s) (hF : ∀ k, Set.range (F k) ⊆ s) :
    Set.range (Path.concat p F) ⊆ s := by
  induction n with
  | zero =>
      rintro z ⟨t, rfl⟩
      simpa only [Path.concat_zero, Path.refl_apply] using hp
  | succ n ih =>
      rw [Path.concat_succ]
      exact (Path.trans_range
        (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) (F (Fin.last n))).subset.trans
          (Set.union_subset
            (ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp (fun k => hF k.castSucc))
            (hF (Fin.last n)))

private theorem exists_different_sphere_point (x : Sphere3) : ∃ p : Sphere3, x ≠ p := by
  by_cases h : x = sourceSphereHomeomorph (1 : SU2)
  · refine ⟨sourceSphereHomeomorph negativeIdentity, ?_⟩
    intro heq
    exact negativeIdentity_ne_one (sourceSphereHomeomorph.injective (h.symm.trans heq)).symm
  · exact ⟨sourceSphereHomeomorph (1 : SU2), h⟩

/-- A representative of an arbitrary loop is replaced by finitely many chart
segments. The omitted point is selected after constructing those segments. -/
theorem sphere_loop_nullhomotopic {x : Sphere3} (γ : Path x x) :
    Path.Homotopic γ (Path.refl x) := by
  classical
  let c (p : Sphere3) : Set I := γ ⁻¹' ({p}ᶜ)
  have hc : ∀ p, IsOpen (c p) := fun p => isOpen_compl_singleton.preimage γ.continuous
  have hcover : Set.univ ⊆ ⋃ p, c p := by
    intro t _
    obtain ⟨p, hp⟩ := exists_different_sphere_point (γ t)
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc hcover
  let τ : Fin (N + 2) → I := fun k => t k
  have hτ0 : τ 0 = 0 := ht0
  have hτ1 : τ (Fin.last (N + 1)) = 1 := hN (N + 1) (Nat.le_succ N)
  choose pole hpole using htcover
  let a : Fin (N + 2) → Sphere3 := γ ∘ τ
  let F (k : Fin (N + 1)) := γ.subpath (τ k.castSucc) (τ k.succ)
  have hF : ∀ k : Fin (N + 1), ∀ s, F k s ≠ pole k := by
    intro k s
    have hmem : F k s ∈ γ '' Set.Icc (t k) (t (k + 1)) := by
      rw [← γ.range_subpath_of_le (t k) (t (k + 1)) (htmono (Nat.le_succ k))]
      exact Set.mem_range_self s
    obtain ⟨u, hu, heq⟩ := hmem
    rw [← heq]
    exact hpole k hu
  let xk (k : Fin (N + 1)) : PuncturedSphere (pole k) :=
    ⟨a k.castSucc, by simpa only [F, a, Function.comp_apply, Path.source] using hF k 0⟩
  let yk (k : Fin (N + 1)) : PuncturedSphere (pole k) :=
    ⟨a k.succ, by simpa only [F, a, Function.comp_apply, Path.target] using hF k 1⟩
  let G (k : Fin (N + 1)) : Path (a k.castSucc) (a k.succ) :=
    chartPath (pole k) (xk k) (yk k)
  have hFG : ∀ k, Path.Homotopic (F k) (G k) := fun k =>
    sphere_paths_homotopic_of_avoid (pole k) (F k) (G k)
      (hF k) (chartPath_avoids _ _ _)
  obtain ⟨q, hq⟩ := exists_sphere_point_outside
    (fun k : Fin (N + 1) => chartSpan (pole k) (a k.castSucc) (a k.succ))
    (fun k => chartSpan_ne_top _ _ _)
  have hG : ∀ k s, G k s ≠ q := by
    intro k s heq
    apply hq k
    rw [← heq]
    exact chartPath_mem_span (pole k) (xk k) (yk k) s
  have ha0 : a 0 ≠ q := by
    intro h
    apply hG 0 0
    exact (G 0).source.trans h
  have hconcat : ∀ s, Path.concat a G s ≠ q := by
    have hrange := concat_range_subset a G {z | z ≠ q} ha0 (fun k z hz => by
      obtain ⟨s, rfl⟩ := hz
      exact hG k s)
    exact fun s => hrange (Set.mem_range_self s)
  have hstart : a 0 = x := by change γ (τ 0) = x; rw [hτ0, γ.source]
  have hend : a (Fin.last (N + 1)) = x := by
    change γ (τ (Fin.last (N + 1))) = x
    rw [hτ1, γ.target]
  let δ : Path x x := (Path.concat a G).cast hstart.symm hend.symm
  have hγδ : Path.Homotopic γ δ := by
    have h₁ := (Path.Homotopic.concat_subpath γ τ).symm
    have h₂ := Path.Homotopic.concat_hcomp a F G hFG
    obtain ⟨H⟩ := h₁.trans h₂
    refine ⟨(H.pathCast hstart.symm hend.symm).cast ?_ rfl⟩
    apply Path.ext
    funext s
    change γ (Set.Icc.convexComb (τ 0) (τ (Fin.last (N + 1))) s) = γ s
    rw [hτ0, hτ1, Set.Icc.convexComb_zero_one]
  exact hγδ.trans (sphere_loop_nullhomotopic_of_avoid q δ hconcat)

theorem sphere_simplyConnected : SimplyConnectedSpace Sphere3 := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  let : PathConnectedSpace SU2 := source_pathConnected
  exact ⟨sourceSphereHomeomorph.pathConnectedSpace, fun _ γ => sphere_loop_nullhomotopic γ⟩

theorem source_simplyConnected : SimplyConnectedSpace SU2 := by
  let : SimplyConnectedSpace Sphere3 := sphere_simplyConnected
  exact sourceSphereHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem sourcePair_simplyConnected : SimplyConnectedSpace SourcePair :=
  sourcePair_simplyConnected_of_source source_simplyConnected

end GeneratedFoundations.Geometry.SourceSimplyConnected
