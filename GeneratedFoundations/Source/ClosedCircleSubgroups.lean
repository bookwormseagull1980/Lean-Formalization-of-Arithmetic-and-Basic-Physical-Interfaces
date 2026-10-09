module

public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Connected closed subgroups of the circle

A closed preconnected subgroup of a circle is either trivial or the whole
circle. The proof excludes finite cyclic subgroups by connectedness and uses
the classification of nondense subgroups of the additive circle.
-/

@[expose] public section

namespace GeneratedFoundations.Source.ClosedCircleSubgroups

theorem additive_eq_bot_or_top {p : ℝ} [Fact (0 < p)]
    (S : AddSubgroup (AddCircle p)) (hclosed : IsClosed (S : Set (AddCircle p)))
    (hconnected : IsPreconnected (S : Set (AddCircle p))) : S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hdense : Dense (S : Set (AddCircle p)) := by
    apply AddCircle.dense_addSubgroup_iff_ne_zmultiples.mpr
    intro a ha hS
    subst S
    let : Finite (AddSubgroup.zmultiples a) :=
      Finite.of_equiv (Fin (addOrderOf a))
        (finEquivZMultiples (addOrderOf_ne_zero_iff.mp ha))
    have hfinite : (AddSubgroup.zmultiples a : Set (AddCircle p)).Finite := Set.toFinite _
    have hsub := hconnected.isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
    apply hbot
    apply (AddSubgroup.eq_bot_iff_forall _).mpr
    intro x hx
    exact hsub hx (AddSubgroup.zero_mem _)
  apply AddSubgroup.coe_eq_univ.mp
  rw [← hclosed.closure_eq, hdense.closure_eq]

theorem multiplicative_eq_bot_or_top (S : Subgroup Circle)
    (hclosed : IsClosed (S : Set Circle))
    (hconnected : IsPreconnected (S : Set Circle)) : S = ⊥ ∨ S = ⊤ := by
  let T : AddSubgroup (AddCircle (1 : ℝ)) :=
    { carrier := AddCircle.toCircle ⁻¹' (S : Set Circle)
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change AddCircle.toCircle (x + y) ∈ S
        rw [AddCircle.toCircle_add]
        exact S.mul_mem hx hy
      neg_mem' := by
        intro x hx
        change AddCircle.toCircle (-x) ∈ S
        rw [AddCircle.toCircle_neg]
        exact S.inv_mem hx }
  have hc : IsClosed (T : Set (AddCircle (1 : ℝ))) :=
    hclosed.preimage AddCircle.continuous_toCircle
  have hp : IsPreconnected (T : Set (AddCircle (1 : ℝ))) := by
    change IsPreconnected (AddCircle.toCircle ⁻¹' (S : Set Circle))
    have he : (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) :
        AddCircle (1 : ℝ) → Circle) = AddCircle.toCircle :=
      funext (AddCircle.homeomorphCircle_apply _)
    simpa only [he] using
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).isPreconnected_preimage.mpr
        hconnected
  rcases additive_eq_bot_or_top T hc hp with ht | ht
  · left
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    obtain ⟨a, ha⟩ :=
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).surjective z
    have ha' : AddCircle.toCircle a = z := by
      simpa only [AddCircle.homeomorphCircle_apply] using ha
    have hat : a ∈ T := by change AddCircle.toCircle a ∈ S; rwa [ha']
    have ha0 : a = 0 := by simpa [ht] using hat
    simpa [ha0] using ha'.symm
  · right
    apply top_unique
    intro z _
    obtain ⟨a, ha⟩ :=
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).surjective z
    have hat : a ∈ T := by simp [ht]
    change AddCircle.toCircle a ∈ S at hat
    simpa only [← AddCircle.homeomorphCircle_apply (one_ne_zero : (1 : ℝ) ≠ 0), ha]
      using hat

theorem surjective_of_compact_connected {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [PreconnectedSpace G] [Nontrivial G]
    (f : G →* Circle) (hcontinuous : Continuous f) (hfaithful : Function.Injective f) :
    Function.Surjective f := by
  have hc : IsClosed (f.range : Set Circle) := by
    simpa only [MonoidHom.coe_range] using (isCompact_range hcontinuous).isClosed
  have hp : IsPreconnected (f.range : Set Circle) := by
    simpa only [MonoidHom.coe_range, Set.image_univ] using
      isPreconnected_univ.image f hcontinuous.continuousOn
  rcases multiplicative_eq_bot_or_top f.range hc hp with h | h
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have hfg : f g = 1 := by
      have hm : f g ∈ f.range := ⟨g, rfl⟩
      simpa [h] using hm
    exact (hg (hfaithful (hfg.trans (map_one f).symm))).elim
  · intro z
    have hz : z ∈ f.range := by simp [h]
    exact hz

end GeneratedFoundations.Source.ClosedCircleSubgroups
