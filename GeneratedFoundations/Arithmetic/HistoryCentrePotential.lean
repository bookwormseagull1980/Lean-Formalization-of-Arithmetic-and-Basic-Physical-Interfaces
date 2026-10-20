module

public import GeneratedFoundations.Arithmetic.HistoryJointCentreResponse
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Restoring potential of the complete generated centre response

The potential is the logarithm of the actual partition on all history,
phase and source coefficients. Its force and curvature are differentiated
from that partition. No mass coefficient or preferred displacement is
supplied. The closed source has its unique stationary point at zero,
where the computed curvature is one. Away from zero the curvature is
positive but is not assigned a displacement-independent lower bound.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryCentrePotential

open HistoryJointCentreResponse

def potential (n : ℕ) (h : ℝ) : ℝ := Real.log (partition n h)

def force (n : ℕ) (h : ℝ) : ℝ := bias n h

theorem potential_zero (n : ℕ) : potential n 0 = 0 := by
  simp [potential, closed_partition]

theorem potential_even (n : ℕ) (h : ℝ) : potential n (-h) = potential n h := by
  rw [potential, potential, partition_even]

theorem potential_nonneg (n : ℕ) (h : ℝ) : 0 ≤ potential n h := by
  rw [potential, partition_eq_cosh]
  exact Real.log_nonneg (Real.one_le_cosh h)

theorem potential_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (potential n) (force n h) h := logPartition_hasDerivAt n h

theorem potential_deriv (n : ℕ) (h : ℝ) : deriv (potential n) h = force n h :=
  (potential_hasDerivAt n h).deriv

theorem force_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (force n) (susceptibility n h) h := bias_hasDerivAt n h

theorem potential_secondDeriv (n : ℕ) (h : ℝ) :
    HasDerivAt (fun u => deriv (potential n) u) (susceptibility n h) h := by
  simpa only [potential_deriv] using force_hasDerivAt n h

theorem secondDeriv_positive (n : ℕ) (h : ℝ) :
    0 < deriv (fun u => deriv (potential n) u) h := by
  rw [(potential_secondDeriv n h).deriv]
  exact susceptibility_pos n h

theorem stationary_iff_zero (n : ℕ) (h : ℝ) :
    deriv (potential n) h = 0 ↔ h = 0 := by
  rw [potential_deriv]
  exact bias_eq_zero_iff n h

theorem equilibrium_curvature (n : ℕ) :
    deriv (fun u => deriv (potential n) u) 0 = 1 := by
  rw [(potential_secondDeriv n 0).deriv, closed_susceptibility]

/-- The equilibrium is fixed by the actual partition response; it is not a
displacement chosen as input. -/
def equilibrium (_n : ℕ) : ℝ := 0

theorem equilibrium_stationary (n : ℕ) :
    deriv (potential n) (equilibrium n) = 0 :=
  (stationary_iff_zero n _).mpr rfl

theorem equilibrium_unique (n : ℕ) (h : ℝ)
    (hh : deriv (potential n) h = 0) : h = equilibrium n :=
  (stationary_iff_zero n h).mp hh

/-- The complete derivative law and the value at zero determine the
potential; an arbitrary additive term is not retained as source data. -/
theorem potential_unique (n : ℕ) (F : ℝ → ℝ) (hF : ∀ h,
    HasDerivAt F (force n h) h) (hzero : F 0 = 0) : F = potential n := by
  have hd (h : ℝ) : HasDerivAt (fun u => F u - potential n u) 0 h := by
    convert! (hF h).sub (potential_hasDerivAt n h) using 1
    simp
  have hconst := is_const_of_deriv_eq_zero
    (fun h => (hd h).differentiableAt) (fun h => (hd h).deriv)
  funext h
  have he := hconst h 0
  rw [hzero, potential_zero] at he
  linarith

theorem potential_ray_secondDeriv_zero (n : ℕ) (v : ℝ) :
    HasDerivAt (fun t : ℝ => deriv (fun u => potential n (u * v)) t) (v ^ 2) 0 := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => potential n (u * v))
      (force n (t * v) * v) t := by
    convert! (potential_hasDerivAt n (t * v)).comp t
      ((hasDerivAt_id t).mul_const v) using 1
    simp only [one_mul]
  have hf := ((force_hasDerivAt n ((0 : ℝ) * v)).comp 0
    ((hasDerivAt_id (0 : ℝ)).mul_const v)).mul_const v
  convert! hf using 1
  · funext t
    exact (hd t).deriv
  · simp [closed_susceptibility, pow_two]

structure Conclusions : Prop where
  nonnegative_potential : ∀ n h, 0 ≤ potential n h
  unique_stationary_point : ∀ n h, deriv (potential n) h = 0 ↔ h = 0
  actual_restoring_curvature : ∀ n h,
    deriv (fun u => deriv (potential n) u) h = susceptibility n h
  positive_curvature : ∀ n h, 0 < deriv (fun u => deriv (potential n) u) h
  unit_equilibrium_curvature : ∀ n, deriv (fun u => deriv (potential n) u) 0 = 1
  actual_equilibrium : ∀ n, deriv (potential n) (equilibrium n) = 0
  computed_equilibrium_unique : ∀ n h, deriv (potential n) h = 0 → h = equilibrium n
  uniquely_integrated : ∀ n F, (∀ h, HasDerivAt F (force n h) h) →
    F 0 = 0 → F = potential n

theorem generated : Conclusions where
  nonnegative_potential := potential_nonneg
  unique_stationary_point := stationary_iff_zero
  actual_restoring_curvature := fun n h => (potential_secondDeriv n h).deriv
  positive_curvature := secondDeriv_positive
  unit_equilibrium_curvature := equilibrium_curvature
  actual_equilibrium := equilibrium_stationary
  computed_equilibrium_unique := equilibrium_unique
  uniquely_integrated := potential_unique

end GeneratedFoundations.Arithmetic.HistoryCentrePotential
