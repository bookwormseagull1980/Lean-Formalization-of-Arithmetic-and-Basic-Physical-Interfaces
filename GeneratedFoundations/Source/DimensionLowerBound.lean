module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Tactic.Linarith

/-!
# The dimension lower bound for reversible change

A connected group acts trivially by real linear isometries in dimension one.
Thus a faithful action of a nontrivial connected group on a nonzero real
finite-dimensional carrier has dimension at least two.
-/

@[expose] public section

namespace GeneratedFoundations.Source.DimensionLowerBound

variable {G V : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [TopologicalSpace G] [PreconnectedSpace G] [FiniteDimensional ℝ V] in
theorem orbit_mem_pair_of_finrank_one (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hdim : Module.finrank ℝ V = 1) (g : G) (v : V) :
    ρ g v ∈ ({v, -v} : Set V) := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hv (ρ g v)
  have hnorm : ‖c‖ * ‖v‖ = 1 * ‖v‖ := by
    rw [← norm_smul, hc, (ρ g).norm_map, one_mul]
  have habs : |c| = |(1 : ℝ)| := by
    simpa using mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) hnorm
  rcases abs_eq_abs.mp habs with h | h
  · simp [← hc, h]
  · simp [← hc, h]

omit [FiniteDimensional ℝ V] in
theorem action_eq_identity_of_finrank_one (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hcontinuous : ∀ v : V, Continuous (fun g : G => ρ g v))
    (hdim : Module.finrank ℝ V = 1) (g : G) : ρ g = 1 := by
  ext v
  have hmaps : Set.MapsTo (fun g : G => ρ g v) Set.univ ({v, -v} : Set V) :=
    fun a _ => orbit_mem_pair_of_finrank_one ρ hdim a v
  have h := isPreconnected_univ.constant_of_mapsTo (Set.toFinite ({v, -v} : Set V)).isDiscrete
    (hcontinuous v).continuousOn hmaps (Set.mem_univ g) (Set.mem_univ (1 : G))
  simpa using h

theorem faithful_connected_dimension_at_least_two [Nontrivial G] [Nontrivial V]
    (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hcontinuous : ∀ v : V, Continuous (fun g : G => ρ g v))
    (hfaithful : Function.Injective ρ) : 2 ≤ Module.finrank ℝ V := by
  have hpos : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Module.finrank ℝ V ≠ 1 := by
    intro hdim
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    apply hg
    apply hfaithful
    simpa using action_eq_identity_of_finrank_one ρ hcontinuous hdim g
  omega

end GeneratedFoundations.Source.DimensionLowerBound
