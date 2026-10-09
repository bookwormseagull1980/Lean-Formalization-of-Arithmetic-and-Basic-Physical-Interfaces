module

public import GeneratedFoundations.Correlation.Endpoints
public import GeneratedFoundations.Spectral.NeumannPoisson
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure

/-!
# The generated finite window as an actual interval interface

The endpoints supplied by the correlation construction determine an ordinary
interval. Affine translation induces measure-preserving `L²` maps between
this interval and the interval beginning at zero. The primitive
characterization of the first derivative gives the corresponding transport
of first- and second-order Sobolev representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

open GeneratedFoundations.Correlation.Endpoints

def windowLeft (b : ℝ) : ℝ := uvEndpoint b

def windowRight (b : ℝ) : ℝ := irEndpoint b

def windowLengthGenerated (b : ℝ) : ℝ := windowRight b - windowLeft b

theorem windowLengthGenerated_eq (b : ℝ) :
    windowLengthGenerated b = windowLength b := rfl

theorem windowLeft_add_length {b : ℝ} (_hb : 0 < b) :
    windowLeft b + windowLengthGenerated b = windowRight b := by
  simp only [windowLeft, windowRight, windowLengthGenerated]
  ring

theorem windowLengthGenerated_pos {b : ℝ} (hb : 0 < b) :
    0 < windowLengthGenerated b := by
  simpa only [windowLengthGenerated_eq] using windowLength_pos hb

def shiftRight (a : ℝ) (x : ℝ) : ℝ := x + a

def shiftLeft (a : ℝ) (x : ℝ) : ℝ := x - a

theorem shiftRight_preimage_Icc {a L : ℝ} :
    shiftRight a ⁻¹' Icc a (a + L) = Icc 0 L := by
  ext x
  simp only [shiftRight, mem_preimage, mem_Icc]
  constructor
  · intro hx
    constructor <;> linarith
  · intro hx
    constructor <;> linarith

theorem shiftLeft_preimage_Icc {a L : ℝ} :
    shiftLeft a ⁻¹' Icc 0 L = Icc a (a + L) := by
  ext x
  simp only [shiftLeft, mem_preimage, mem_Icc]
  constructor
  · intro hx
    constructor <;> linarith
  · intro hx
    constructor <;> linarith

theorem shiftRight_measurePreserving {a L : ℝ} :
    MeasurePreserving (shiftRight a) (intervalMeasure 0 L)
      (intervalMeasure a (a + L)) := by
  have h : MeasurePreserving (shiftRight a) (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume a
  simpa only [intervalMeasure, shiftRight_preimage_Icc] using
    h.restrict_preimage (s := Icc a (a + L)) measurableSet_Icc

theorem shiftLeft_measurePreserving {a L : ℝ} :
    MeasurePreserving (shiftLeft a) (intervalMeasure a (a + L))
      (intervalMeasure 0 L) := by
  have h : MeasurePreserving (shiftLeft a) (volume : Measure ℝ) volume :=
    measurePreserving_sub_right volume a
  simpa only [intervalMeasure, shiftLeft_preimage_Icc] using
    h.restrict_preimage (s := Icc 0 L) measurableSet_Icc

noncomputable def shiftToCanonicalL2 (a L : ℝ) :
    ComplexIntervalL2 a (a + L) →ₗᵢ[ℂ] ComplexIntervalL2 0 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (shiftRight a)
    (shiftRight_measurePreserving (a := a) (L := L))

noncomputable def shiftFromCanonicalL2 (a L : ℝ) :
    ComplexIntervalL2 0 L →ₗᵢ[ℂ] ComplexIntervalL2 a (a + L) :=
  Lp.compMeasurePreservingₗᵢ ℂ (shiftLeft a)
    (shiftLeft_measurePreserving (a := a) (L := L))

@[simp] theorem shiftToCanonicalL2_apply_toLp {a L : ℝ}
    {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure a (a + L))) :
    shiftToCanonicalL2 a L (hf.toLp f) =
      (hf.comp_measurePreserving (shiftRight_measurePreserving (a := a) (L := L))).toLp
        (fun x => f (shiftRight a x)) := rfl

@[simp] theorem shiftFromCanonicalL2_apply_toLp {a L : ℝ}
    {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure 0 L)) :
    shiftFromCanonicalL2 a L (hf.toLp f) =
      (hf.comp_measurePreserving (shiftLeft_measurePreserving (a := a) (L := L))).toLp
        (fun x => f (shiftLeft a x)) := rfl

theorem translate_h1 {a L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ} (h : HasComplexH1Derivative a (a + L) f g) :
    HasComplexH1Derivative 0 L (fun x => f (shiftRight a x))
      (fun x => g (shiftRight a x)) := by
  have hg : MemLp (fun x => g (shiftRight a x)) 2 (intervalMeasure 0 L) :=
    h.derivative_memLp.comp_measurePreserving
      (shiftRight_measurePreserving (a := a) (L := L))
  apply hasComplexH1Derivative_of_primitive hL hg
  intro x hx
  have hx' : shiftRight a x ∈ Icc a (a + L) := by
    constructor <;> dsimp [shiftRight] <;> linarith [hx.1, hx.2]
  have hfx := h.integral_eq_sub ⟨le_rfl, by linarith⟩ hx'
  calc
    f (shiftRight a x) = f a + (f (shiftRight a x) - f a) := by ring
    _ = f a + (∫ z in a..shiftRight a x, g z) := by rw [hfx]
    _ = f (shiftRight a 0) + (∫ z in 0..x, g (shiftRight a z)) := by
      simp only [shiftRight, intervalIntegral.integral_comp_add_right, zero_add]

def translateRepresentative {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative a (a + L)) :
    ComplexH2Representative 0 L where
  value := fun x => f.value (shiftRight a x)
  first := fun x => f.first (shiftRight a x)
  second := fun x => f.second (shiftRight a x)
  firstDerivative := translate_h1 hL f.firstDerivative
  secondDerivative := translate_h1 hL f.secondDerivative

theorem translateRepresentative_toL2 {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative a (a + L)) :
    (translateRepresentative hL f).toL2 =
      shiftToCanonicalL2 a L f.toL2 := rfl

theorem translateRepresentative_secondL2 {a L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative a (a + L)) :
    (translateRepresentative hL f).secondL2 =
      shiftToCanonicalL2 a L f.secondL2 := rfl

def generatedWindowRepresentative {b : ℝ} (hb : 0 < b)
    (f : ComplexH2Representative (windowLeft b) (windowRight b)) :
    ComplexH2Representative 0 (windowLengthGenerated b) := by
  have hL : 0 < windowLengthGenerated b := windowLengthGenerated_pos hb
  have heq : windowLeft b + windowLengthGenerated b = windowRight b :=
    windowLeft_add_length hb
  exact translateRepresentative hL (heq.symm ▸ f)

end GeneratedFoundations.Spectral
