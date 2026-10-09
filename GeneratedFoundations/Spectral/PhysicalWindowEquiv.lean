module

public import GeneratedFoundations.Spectral.PhysicalWindowNeumann

/-!
# Two-sided interval transport

The inverse affine maps induce inverse `L²` linear isometries and an
equivalence of the represented Neumann domains. Domain equality is equality
of `L²` values, independent of the representatives used to construct the maps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

theorem shiftRight_comp_shiftLeft (a : ℝ) (x : ℝ) :
    shiftRight a (shiftLeft a x) = x := by
  dsimp [shiftRight, shiftLeft]
  ring

theorem shiftLeft_comp_shiftRight (a : ℝ) (x : ℝ) :
    shiftLeft a (shiftRight a x) = x := by
  dsimp [shiftRight, shiftLeft]
  ring

theorem shiftRight_comp_shiftLeft_eq_id (a : ℝ) :
    shiftRight a ∘ shiftLeft a = id := by
  funext x
  exact shiftRight_comp_shiftLeft a x

theorem shiftLeft_comp_shiftRight_eq_id (a : ℝ) :
    shiftLeft a ∘ shiftRight a = id := by
  funext x
  exact shiftLeft_comp_shiftRight a x

theorem shiftRightLeft_measurePreserving {a L : ℝ} :
    MeasurePreserving (shiftRight a ∘ shiftLeft a)
      (intervalMeasure a (a + L)) (intervalMeasure a (a + L)) := by
  have h := (shiftRight_measurePreserving (a := a) (L := L)).comp
    (shiftLeft_measurePreserving (a := a) (L := L))
  simpa only [Function.comp_def, shiftRight_comp_shiftLeft] using h

theorem shiftLeftRight_measurePreserving {a L : ℝ} :
    MeasurePreserving (shiftLeft a ∘ shiftRight a)
      (intervalMeasure 0 L) (intervalMeasure 0 L) := by
  have h := (shiftLeft_measurePreserving (a := a) (L := L)).comp
    (shiftRight_measurePreserving (a := a) (L := L))
  simpa only [Function.comp_def, shiftLeft_comp_shiftRight] using h

noncomputable def shiftCanonicalL2Equiv {a L : ℝ} :
    ComplexIntervalL2 a (a + L) ≃ₗᵢ[ℂ] ComplexIntervalL2 0 L :=
  LinearIsometryEquiv.ofLinearIsometry (shiftToCanonicalL2 a L)
    (shiftFromCanonicalL2 a L).toLinearMap (by
      apply LinearMap.ext
      intro u
      change shiftToCanonicalL2 a L (shiftFromCanonicalL2 a L u) = u
      change Lp.compMeasurePreserving (shiftRight a)
          (shiftRight_measurePreserving (a := a) (L := L))
          (Lp.compMeasurePreserving (shiftLeft a)
            (shiftLeft_measurePreserving (a := a) (L := L)) u) = u
      rw [← Lp.compMeasurePreserving_comp_apply u
        (shiftLeft_measurePreserving (a := a) (L := L))
        (shiftRight_measurePreserving (a := a) (L := L))]
      simpa only [shiftLeft_comp_shiftRight_eq_id] using
        Lp.compMeasurePreserving_id_apply u) (by
      apply LinearMap.ext
      intro u
      change shiftFromCanonicalL2 a L (shiftToCanonicalL2 a L u) = u
      change Lp.compMeasurePreserving (shiftLeft a)
          (shiftLeft_measurePreserving (a := a) (L := L))
          (Lp.compMeasurePreserving (shiftRight a)
            (shiftRight_measurePreserving (a := a) (L := L)) u) = u
      rw [← Lp.compMeasurePreserving_comp_apply u
        (shiftRight_measurePreserving (a := a) (L := L))
        (shiftLeft_measurePreserving (a := a) (L := L))]
      simpa only [shiftRight_comp_shiftLeft_eq_id] using
        Lp.compMeasurePreserving_id_apply u)

@[simp] theorem shiftCanonicalL2Equiv_apply {a L : ℝ} (u : ComplexIntervalL2 a (a + L)) :
    shiftCanonicalL2Equiv u = shiftToCanonicalL2 a L u := rfl

@[simp] theorem shiftCanonicalL2Equiv_symm_apply {a L : ℝ}
    (u : ComplexIntervalL2 0 L) :
    (shiftCanonicalL2Equiv (a := a) (L := L)).symm u = shiftFromCanonicalL2 a L u := rfl

noncomputable def translateNeumannDomainEquiv {a L : ℝ} (hL : 0 < L) :
    complexNeumannDomain a (a + L) ≃ complexNeumannDomain 0 L where
  toFun := translateNeumannDomain hL
  invFun := translateBackNeumannDomain hL
  left_inv := by
    intro u
    apply Subtype.ext
    rw [translateBackNeumannDomain_toL2, translateNeumannDomain_toL2]
    exact (shiftCanonicalL2Equiv (a := a) (L := L)).symm_apply_apply u
  right_inv := by
    intro u
    apply Subtype.ext
    rw [translateNeumannDomain_toL2, translateBackNeumannDomain_toL2]
    exact (shiftCanonicalL2Equiv (a := a) (L := L)).apply_symm_apply u

theorem translateNeumannDomainEquiv_toL2 {a L : ℝ} (hL : 0 < L)
    (u : complexNeumannDomain a (a + L)) :
    ((translateNeumannDomainEquiv hL u : complexNeumannDomain 0 L) :
      ComplexIntervalL2 0 L) =
        shiftCanonicalL2Equiv (a := a) (L := L) (u : ComplexIntervalL2 a (a + L)) := by
  exact translateNeumannDomain_toL2 hL u

end GeneratedFoundations.Spectral
