module

public import GeneratedFoundations.Spectral.PhysicalWindowInterface

/-!
# Neumann representatives on the generated window

Endpoint traces of second-order Sobolev representatives are transported by
`x ↦ x+a` and `x ↦ x-a`. These translations induce maps in both directions
between the Neumann domains, and their underlying `L²` maps are the
measure-preserving translations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

theorem translateNeumannRepresentative {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative a (a + L)) (hf : IsComplexNeumann f) :
    IsComplexNeumann (translateRepresentative hL f) := by
  refine ⟨?_, ?_⟩
  · simpa [translateRepresentative, shiftRight] using hf.1
  · simpa [translateRepresentative, shiftRight, add_comm] using hf.2

theorem translateBack_h1 {a L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ} (h : HasComplexH1Derivative 0 L f g) :
    HasComplexH1Derivative a (a + L) (fun x => f (shiftLeft a x))
      (fun x => g (shiftLeft a x)) := by
  have hg : MemLp (fun x => g (shiftLeft a x)) 2 (intervalMeasure a (a + L)) :=
    h.derivative_memLp.comp_measurePreserving
      (shiftLeft_measurePreserving (a := a) (L := L))
  apply hasComplexH1Derivative_of_primitive (by linarith) hg
  intro x hx
  have hx' : shiftLeft a x ∈ Icc 0 L := by
    constructor <;> dsimp [shiftLeft] <;> linarith [hx.1, hx.2]
  have hfx := h.integral_eq_sub ⟨le_rfl, hL.le⟩ hx'
  calc
    f (shiftLeft a x) = f 0 + (f (shiftLeft a x) - f 0) := by ring
    _ = f 0 + (∫ z in 0..shiftLeft a x, g z) := by rw [hfx]
    _ = f (shiftLeft a a) + (∫ z in a..x, g (shiftLeft a z)) := by
      simp only [shiftLeft, intervalIntegral.integral_comp_sub_right, sub_self]

def translateBackRepresentative {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) :
    ComplexH2Representative a (a + L) where
  value := fun x => f.value (shiftLeft a x)
  first := fun x => f.first (shiftLeft a x)
  second := fun x => f.second (shiftLeft a x)
  firstDerivative := translateBack_h1 hL f.firstDerivative
  secondDerivative := translateBack_h1 hL f.secondDerivative

theorem translateBackNeumannRepresentative {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) (hf : IsComplexNeumann f) :
    IsComplexNeumann (translateBackRepresentative (a := a) hL f) := by
  refine ⟨?_, ?_⟩
  · simpa [translateBackRepresentative, shiftLeft] using hf.1
  · simpa [translateBackRepresentative, shiftLeft] using hf.2

theorem translateBackRepresentative_toL2 {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) :
    (translateBackRepresentative hL f).toL2 =
      shiftFromCanonicalL2 a L f.toL2 := rfl

theorem translateBackRepresentative_secondL2 {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) :
    (translateBackRepresentative hL f).secondL2 =
      shiftFromCanonicalL2 a L f.secondL2 := rfl

noncomputable def translateNeumannDomain {a L : ℝ} (hL : 0 < L) :
    complexNeumannDomain a (a + L) → complexNeumannDomain 0 L := fun u =>
  let f := complexNeumannRepresentative u
  ⟨(translateRepresentative hL f).toL2,
    ⟨translateRepresentative hL f, translateNeumannRepresentative hL f
      (complexNeumannRepresentative_spec u).1, rfl⟩⟩

noncomputable def translateBackNeumannDomain {a L : ℝ} (hL : 0 < L) :
    complexNeumannDomain 0 L → complexNeumannDomain a (a + L) := fun u =>
  let f := complexNeumannRepresentative u
  ⟨(translateBackRepresentative hL f).toL2,
    ⟨translateBackRepresentative hL f,
      translateBackNeumannRepresentative hL f
        (complexNeumannRepresentative_spec u).1, rfl⟩⟩

theorem translateNeumannDomain_toL2 {a L : ℝ} (hL : 0 < L)
    (u : complexNeumannDomain a (a + L)) :
    (translateNeumannDomain hL u : ComplexIntervalL2 0 L) =
      shiftToCanonicalL2 a L (u : ComplexIntervalL2 a (a + L)) := by
  change (translateRepresentative hL (complexNeumannRepresentative u)).toL2 = _
  rw [translateRepresentative_toL2, (complexNeumannRepresentative_spec u).2]

theorem translateBackNeumannDomain_toL2 {a L : ℝ} (hL : 0 < L)
    (u : complexNeumannDomain 0 L) :
    (translateBackNeumannDomain (a := a) hL u : ComplexIntervalL2 a (a + L)) =
      shiftFromCanonicalL2 a L (u : ComplexIntervalL2 0 L) := by
  change (translateBackRepresentative hL (complexNeumannRepresentative u)).toL2 = _
  rw [translateBackRepresentative_toL2, (complexNeumannRepresentative_spec u).2]

end GeneratedFoundations.Spectral
