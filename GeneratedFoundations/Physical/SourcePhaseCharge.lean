module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Phase charge of a retained real matter pair

The common coefficient of the two real components gives a rotational
source work identity.  The identity is proved before using either field
equation.  On their common equation the phase charge has zero derivative,
even when the volume and source dependent kinetic coefficient vary.
The functions below are solution coordinates, not additional root data.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourcePhaseCharge

def charge (W x y vx vy : ℝ) : ℝ := W * (x * vy - y * vx)

/-- The complete algebraic identity retains the two field equation
residuals.  It therefore also measures their effect in an approximate
evolution, without assuming exact conservation in that evolution. -/
theorem phase_work_identity (W dW B x y vx vy ax ay : ℝ) :
    dW * (x * vy - y * vx) + W * (x * ay - y * ax) =
      x * (W * ay + dW * vy + B * y) -
      y * (W * ax + dW * vx + B * x) := by
  ring

theorem phase_charge_derivative
    (W x y vx vy : ℝ → ℝ) (t dW ax ay : ℝ)
    (hW : HasDerivAt W dW t)
    (hx : HasDerivAt x (vx t) t) (hy : HasDerivAt y (vy t) t)
    (hvx : HasDerivAt vx ax t) (hvy : HasDerivAt vy ay t) :
    HasDerivAt (fun u => charge (W u) (x u) (y u) (vx u) (vy u))
      (dW * (x t * vy t - y t * vx t) + W t * (x t * ay - y t * ax)) t := by
  convert hW.mul ((hx.mul hvy).sub (hy.mul hvx)) using 1
  · funext u
    rfl
  · dsimp only [Pi.mul_apply, Pi.sub_apply]
    ring

/-- Both components obey the same source dependent equation.  Here
W=a^3 M and B is the potential coefficient including the same volume. -/
theorem phase_charge_conservation
    (W x y vx vy : ℝ → ℝ) (t dW ax ay B : ℝ)
    (hW : HasDerivAt W dW t)
    (hx : HasDerivAt x (vx t) t) (hy : HasDerivAt y (vy t) t)
    (hvx : HasDerivAt vx ax t) (hvy : HasDerivAt vy ay t)
    (ex : W t * ax + dW * vx t + B * x t = 0)
    (ey : W t * ay + dW * vy t + B * y t = 0) :
    HasDerivAt (fun u => charge (W u) (x u) (y u) (vx u) (vy u)) 0 t := by
  have h := phase_charge_derivative W x y vx vy t dW ax ay hW hx hy hvx hvy
  have hz := phase_work_identity (W t) dW B (x t) (y t) (vx t) (vy t) ax ay
  rw [ex, ey, mul_zero, mul_zero, sub_self] at hz
  rwa [hz] at h

/-- The regular positive-charge branch has a positive angular rate.
These inequalities concern the solution interval, not the root source. -/
theorem phase_rate_pos (Q volume kinetic amplitudeSquared : ℝ)
    (hQ : 0 < Q) (hv : 0 < volume) (hM : 0 < kinetic) (hr : 0 < amplitudeSquared) :
    0 < Q / (volume * kinetic * amplitudeSquared) :=
  div_pos hQ (mul_pos (mul_pos hv hM) hr)

end GeneratedFoundations.Physical.SourcePhaseCharge
