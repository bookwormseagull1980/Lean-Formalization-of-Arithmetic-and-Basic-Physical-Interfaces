module

public import GeneratedFoundations.Correlation.Endpoints
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Coordinate form of the generated active window

The two generated endpoints determine an interval of separations. This file
records the affine coordinate sending the left endpoint to zero and the right
endpoint to the interval length. These two normalizations determine its two
coefficients uniquely. The coordinate is a separation coordinate.
-/

@[expose] public section

noncomputable section

open Set Topology
open GeneratedFoundations.Correlation.Endpoints

namespace GeneratedFoundations.Correlation.PhysicalWindowCoordinate

def windowStart (b : ℝ) : ℝ := uvEndpoint b

def windowEnd (b : ℝ) : ℝ := irEndpoint b

def windowCoordinate (b : ℝ) (x : ℝ) : ℝ := x - windowStart b

def windowCoordinateInv (b : ℝ) (y : ℝ) : ℝ := y + windowStart b

theorem windowStart_lt_end {b : ℝ} (hb : 0 < b) :
    windowStart b < windowEnd b := by
  exact sub_pos.mp (windowLength_pos hb)

theorem windowCoordinate_mem {b : ℝ} (_hb : 0 < b)
    {x : ℝ} (hx : x ∈ activeWindow b) :
    windowCoordinate b x ∈ Icc 0 (windowLength b) := by
  change uvEndpoint b ≤ x ∧ x ≤ irEndpoint b at hx
  rcases hx with ⟨hlo, hhi⟩
  change 0 ≤ x - uvEndpoint b ∧ x - uvEndpoint b ≤ irEndpoint b - uvEndpoint b
  constructor
  · linarith
  · linarith

theorem windowCoordinateInv_mem {b : ℝ} (_hb : 0 < b)
    {y : ℝ} (hy : y ∈ Icc 0 (windowLength b)) :
    windowCoordinateInv b y ∈ activeWindow b := by
  rcases hy with ⟨hlo, hhi⟩
  change y ≤ irEndpoint b - uvEndpoint b at hhi
  change uvEndpoint b ≤ y + uvEndpoint b ∧ y + uvEndpoint b ≤ irEndpoint b
  constructor
  · linarith
  · linarith

def windowCoordinateHomeomorph (b : ℝ) (hb : 0 < b) :
    activeWindow b ≃ₜ Icc (0 : ℝ) (windowLength b) where
  toFun x := ⟨windowCoordinate b x, windowCoordinate_mem hb x.property⟩
  invFun y := ⟨windowCoordinateInv b y, windowCoordinateInv_mem hb y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp [windowCoordinate, windowCoordinateInv]
  right_inv y := by
    apply Subtype.ext
    simp [windowCoordinate, windowCoordinateInv]
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.sub continuous_const
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.add continuous_const

@[simp] theorem windowCoordinateHomeomorph_apply (b : ℝ) (hb : 0 < b)
    (x : activeWindow b) :
    windowCoordinateHomeomorph b hb x =
      ⟨x - uvEndpoint b, windowCoordinate_mem hb x.property⟩ := rfl

@[simp] theorem windowCoordinateHomeomorph_symm_apply (b : ℝ) (hb : 0 < b)
    (y : Icc (0 : ℝ) (windowLength b)) :
    (windowCoordinateHomeomorph b hb).symm y =
      ⟨y + uvEndpoint b, windowCoordinateInv_mem hb y.property⟩ := rfl

theorem windowCoordinate_endpoint_zero {b : ℝ} (_hb : 0 < b) :
    windowCoordinate b (uvEndpoint b) = 0 := by
  simp [windowCoordinate, windowStart]

theorem windowCoordinate_endpoint_length {b : ℝ} (_hb : 0 < b) :
    windowCoordinate b (irEndpoint b) = windowLength b := by
  simp [windowCoordinate, windowStart, windowLength]

/-- Equality of coordinates determines the interval homeomorphism. -/
theorem windowCoordinateHomeomorph_ext {b : ℝ} (hb : 0 < b)
    (f : activeWindow b ≃ₜ Icc (0 : ℝ) (windowLength b))
    (hf : ∀ x : activeWindow b, (f x : ℝ) = windowCoordinate b x) :
    f = windowCoordinateHomeomorph b hb := by
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  exact hf x

/-- The two endpoint normalizations determine both affine coefficients. -/
theorem windowCoordinate_affine_coefficients_unique {b : ℝ} (hb : 0 < b)
    (p q : ℝ) (hstart : p * windowStart b + q = 0)
    (hend : p * windowEnd b + q = windowLength b) :
    p = 1 ∧ q = -windowStart b := by
  have hlen : 0 < windowEnd b - windowStart b :=
    sub_pos.mpr (windowStart_lt_end hb)
  have hmul : p * (windowEnd b - windowStart b) =
      1 * (windowEnd b - windowStart b) := by
    change p * windowEnd b + q = windowEnd b - windowStart b at hend
    nlinarith [hstart, hend]
  have hp : p = 1 := mul_right_cancel₀ hlen.ne' hmul
  refine ⟨hp, ?_⟩
  rw [hp, one_mul] at hstart
  linarith

theorem windowCoordinate_affine_unique {b : ℝ} (hb : 0 < b)
    (p q : ℝ) (hstart : p * windowStart b + q = 0)
    (hend : p * windowEnd b + q = windowLength b) :
    (fun x : ℝ => p * x + q) = windowCoordinate b := by
  rcases windowCoordinate_affine_coefficients_unique hb p q hstart hend with ⟨rfl, rfl⟩
  funext x
  simp [windowCoordinate, sub_eq_add_neg]

theorem windowCoordinate_unique {b : ℝ} (hb : 0 < b)
    (f : activeWindow b ≃ₜ Icc (0 : ℝ) (windowLength b))
    (p q : ℝ) (hf : ∀ x : activeWindow b, (f x : ℝ) = p * x + q)
    (hstart : p * windowStart b + q = 0)
    (hend : p * windowEnd b + q = windowLength b) :
    f = windowCoordinateHomeomorph b hb := by
  apply windowCoordinateHomeomorph_ext hb f
  intro x
  rw [hf x]
  exact congrFun (windowCoordinate_affine_unique hb p q hstart hend) x

theorem activeWindow_length {b : ℝ} (_hb : 0 < b) :
    windowEnd b - windowStart b = windowLength b := by
  simp [windowEnd, windowStart, windowLength]

theorem activeWindow_scale {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    windowStart (a * b) = a * windowStart b ∧
      windowEnd (a * b) = a * windowEnd b ∧
      windowLength (a * b) = a * windowLength b := by
  refine ⟨uvEndpoint_dilation hb ha, irEndpoint_dilation hb ha, ?_⟩
  simp only [windowLength, uvEndpoint_dilation hb ha, irEndpoint_dilation hb ha]
  ring

end GeneratedFoundations.Correlation.PhysicalWindowCoordinate
