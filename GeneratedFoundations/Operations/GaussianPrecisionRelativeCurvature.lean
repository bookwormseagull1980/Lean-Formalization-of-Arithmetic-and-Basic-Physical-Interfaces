module

public import GeneratedFoundations.Operations.GaussianPrecisionKL
public import Mathlib.Tactic

/-!
# Relative entropy along a nonlinear scalar precision path

The complete path `p + v*s + w*s²/2` varies the precision of the same
real Gaussian coefficient. The reference action expectation retains its
direct second vertex `w/(2p)`. The negative logarithmic partition retains
the same term, together with its connected fluctuation. Their difference
is the actual relative entropy, whose Hessian is `v²/(2p²)`.

Only positivity of the reference precision is assumed. Positivity of the
varied precision near the reference follows from continuity, so arbitrary
real first and second vertices are allowed.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Operations.GaussianPrecisionRelativeCurvature

open GaussianPrecisionKL

def pathPrecision (p v w s : ℝ) : ℝ := p + v * s + w * s ^ 2 / 2

def pathVelocity (v w s : ℝ) : ℝ := v + w * s

@[simp] theorem pathPrecision_zero (p v w : ℝ) : pathPrecision p v w 0 = p := by
  simp [pathPrecision]

@[simp] theorem pathVelocity_zero (v w : ℝ) : pathVelocity v w 0 = v := by
  simp [pathVelocity]

theorem pathPrecision_hasDerivAt (p v w s : ℝ) :
    HasDerivAt (pathPrecision p v w) (pathVelocity v w s) s := by
  convert! ((hasDerivAt_const s p).add ((hasDerivAt_id s).const_mul v)).add
    ((((hasDerivAt_id s).pow 2).const_mul w).div_const 2) using 1
  simp only [pathVelocity, id_eq]
  ring

theorem pathVelocity_hasDerivAt (v w s : ℝ) :
    HasDerivAt (pathVelocity v w) w s := by
  change HasDerivAt (fun t => v + w * t) w s
  convert! (hasDerivAt_const s v).add ((hasDerivAt_id s).const_mul w) using 1
  ring

theorem pathPrecision_eventually_pos {p : ℝ} (hp : 0 < p) (v w : ℝ) :
    ∀ᶠ s in nhds (0 : ℝ), 0 < pathPrecision p v w s := by
  have hc : Continuous (pathPrecision p v w) := by unfold pathPrecision; fun_prop
  exact (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)

/-- The complete action difference is averaged in the unchanged source law. -/
def referenceActionMean (p v w s : ℝ) : ℝ :=
  ∫ x : ℝ, (pathPrecision p v w s - p) * x ^ 2 / 2 ∂law p

theorem referenceActionMean_eq {p : ℝ} (hp : 0 < p) (v w s : ℝ) :
    referenceActionMean p v w s = (pathPrecision p v w s - p) / (2 * p) := by
  rw [referenceActionMean, integral_div, integral_const_mul, square_integral hp]
  field_simp

def negativeLogPartition (p v w s : ℝ) : ℝ :=
  (Real.log (pathPrecision p v w s) - Real.log p) / 2

def relativePath (p v w s : ℝ) : ℝ :=
  referenceActionMean p v w s - negativeLogPartition p v w s

theorem referenceActionMean_hasDerivAt {p : ℝ} (hp : 0 < p) (v w s : ℝ) :
    HasDerivAt (referenceActionMean p v w)
      (pathVelocity v w s / (2 * p)) s := by
  have hd := ((pathPrecision_hasDerivAt p v w s).sub_const p).div_const (2 * p)
  convert! hd using 1
  funext t
  exact referenceActionMean_eq hp v w t

theorem referenceActionMean_secondDeriv_zero {p : ℝ} (hp : 0 < p) (v w : ℝ) :
    HasDerivAt (fun s => deriv (referenceActionMean p v w) s) (w / (2 * p)) 0 := by
  have hd := (pathVelocity_hasDerivAt v w 0).div_const (2 * p)
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun s =>
    (referenceActionMean_hasDerivAt hp v w s).deriv)

theorem negativeLogPartition_hasDerivAt {p v w s : ℝ}
    (hs : pathPrecision p v w s ≠ 0) :
    HasDerivAt (negativeLogPartition p v w)
      (pathVelocity v w s / (2 * pathPrecision p v w s)) s := by
  have hd := (((pathPrecision_hasDerivAt p v w s).log hs).sub_const
    (Real.log p)).div_const 2
  convert! hd using 1
  ring

/-- The second vertex is present in the partition Hessian before the
reference action is included. -/
theorem negativeLogPartition_secondDeriv_zero {p : ℝ} (hp : 0 < p) (v w : ℝ) :
    HasDerivAt (fun s => deriv (negativeLogPartition p v w) s)
      (w / (2 * p) - v ^ 2 / (2 * p ^ 2)) 0 := by
  have hd := (pathVelocity_hasDerivAt v w 0).div
    ((pathPrecision_hasDerivAt p v w 0).const_mul 2)
      (by simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hp.ne')
  have he : HasDerivAt (fun s => pathVelocity v w s /
      (2 * pathPrecision p v w s))
        (w / (2 * p) - v ^ 2 / (2 * p ^ 2)) 0 := by
    convert! hd using 1
    · simp only [pathPrecision_zero, pathVelocity_zero]
      field_simp
  apply he.congr_of_eventuallyEq
  filter_upwards [pathPrecision_eventually_pos hp v w] with s hs
  exact (negativeLogPartition_hasDerivAt hs.ne').deriv

theorem relativePath_hasDerivAt {p : ℝ} (hp : 0 < p) {v w s : ℝ}
    (hs : pathPrecision p v w s ≠ 0) :
    HasDerivAt (relativePath p v w)
      (pathVelocity v w s / (2 * p) -
        pathVelocity v w s / (2 * pathPrecision p v w s)) s := by
  exact (referenceActionMean_hasDerivAt hp v w s).sub
    (negativeLogPartition_hasDerivAt hs)

/-- The direct second vertex cancels in the complete relative likelihood. -/
theorem relativePath_secondDeriv_zero {p : ℝ} (hp : 0 < p) (v w : ℝ) :
    HasDerivAt (fun s => deriv (relativePath p v w) s) (v ^ 2 / (2 * p ^ 2)) 0 := by
  have hd := (referenceActionMean_secondDeriv_zero hp v w).sub
    (negativeLogPartition_secondDeriv_zero hp v w)
  have he : HasDerivAt (fun s => deriv (referenceActionMean p v w) s -
      deriv (negativeLogPartition p v w) s) (v ^ 2 / (2 * p ^ 2)) 0 := by
    convert! hd using 1
    ring
  apply he.congr_of_eventuallyEq
  filter_upwards [pathPrecision_eventually_pos hp v w] with s hs
  rw [(referenceActionMean_hasDerivAt hp v w s).deriv,
    (negativeLogPartition_hasDerivAt hs.ne').deriv]
  exact (relativePath_hasDerivAt hp hs.ne').deriv

theorem relativePath_eq_kl {p v w s : ℝ} (hp : 0 < p)
    (hs : 0 < pathPrecision p v w s) :
    relativePath p v w s =
      (InformationTheory.klDiv (law p) (law (pathPrecision p v w s))).toReal := by
  rw [klDiv_toReal hp hs, relativePath, referenceActionMean_eq hp,
    negativeLogPartition, Real.log_div hs.ne' hp.ne']
  field_simp

theorem relativePath_eq_llr_integral {p v w s : ℝ} (hp : 0 < p)
    (hs : 0 < pathPrecision p v w s) :
    relativePath p v w s =
      ∫ x, llr (law p) (law (pathPrecision p v w s)) x ∂law p := by
  rw [integral_llr hp hs, relativePath, referenceActionMean_eq hp,
    negativeLogPartition, Real.log_div hs.ne' hp.ne']
  field_simp

/-- The theorem concerns the actual relative entropy of the two Gaussian
measures, not only a formal compensated-log expression. -/
theorem actualKL_secondDeriv_zero {p : ℝ} (hp : 0 < p) (v w : ℝ) :
    HasDerivAt (fun s => deriv (fun t =>
      (InformationTheory.klDiv (law p) (law (pathPrecision p v w t))).toReal) s)
        (v ^ 2 / (2 * p ^ 2)) 0 := by
  have hsame :
      (fun s => (InformationTheory.klDiv (law p)
        (law (pathPrecision p v w s))).toReal) =ᶠ[nhds 0] relativePath p v w := by
    filter_upwards [pathPrecision_eventually_pos hp v w] with s hs
    exact (relativePath_eq_kl hp hs).symm
  exact (relativePath_secondDeriv_zero hp v w).congr_of_eventuallyEq hsame.deriv

end GeneratedFoundations.Operations.GaussianPrecisionRelativeCurvature
