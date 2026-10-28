module

public import GeneratedFoundations.Operations.HermiteSource

/-!
# The least carrier of the vacuum and its first differential variation

The first variation is the actual Gaussian raising differential. The existing
`raising_ground` theorem identifies its representative with `firstProfile`.
Thus the least linear carrier containing these two vectors is the source
corner already used by the physical construction. The comparison here is
between subspaces containing this specified first variation; it does not
identify a finite corner with the full invariant domain of the ladder.
-/

@[expose] public section
noncomputable section

namespace GeneratedFoundations.Operations.SourceCornerMinimality

open HermiteSource GeneratedFoundations.Correlation.ComplexGaussianStates

def firstVariation {b : ℝ} (hb : 0 < b) : ComplexL2 := firstState hb

theorem firstVariation_differential {b : ℝ} (hb : 0 < b) :
    firstVariation hb =ᵐ[MeasureTheory.volume]
      raising b (fun y => (groundProfile b y : ℂ)) := by
  rw [raising_ground hb]
  exact firstState_coe hb

def ContainsFirstVariation {b : ℝ} (hb : 0 < b)
    (P : Submodule ℂ ComplexL2) : Prop :=
  groundState hb ∈ P ∧ firstVariation hb ∈ P

theorem sourceSpace_le_iff {b : ℝ} (hb : 0 < b)
    (P : Submodule ℂ ComplexL2) :
    sourceSpace hb ≤ P ↔ ContainsFirstVariation hb P := by
  rw [sourceSpace_eq_span, Submodule.span_le]
  constructor
  · intro h
    exact ⟨h ⟨0, rfl⟩, h ⟨1, rfl⟩⟩
  · rintro ⟨h0, h1⟩ _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1

theorem sourceSpace_contains {b : ℝ} (hb : 0 < b) :
    ContainsFirstVariation hb (sourceSpace hb) :=
  (sourceSpace_le_iff hb _).mp le_rfl

theorem sourceSpace_isLeast {b : ℝ} (hb : 0 < b) :
    IsLeast {P : Submodule ℂ ComplexL2 | ContainsFirstVariation hb P}
      (sourceSpace hb) :=
  ⟨sourceSpace_contains hb, fun P hP => (sourceSpace_le_iff hb P).mpr hP⟩

theorem least_carrier_unique {b : ℝ} (hb : 0 < b)
    (P : Submodule ℂ ComplexL2)
    (hP : IsLeast {Q : Submodule ℂ ComplexL2 | ContainsFirstVariation hb Q} P) :
    P = sourceSpace hb :=
  hP.unique (sourceSpace_isLeast hb)

end GeneratedFoundations.Operations.SourceCornerMinimality
