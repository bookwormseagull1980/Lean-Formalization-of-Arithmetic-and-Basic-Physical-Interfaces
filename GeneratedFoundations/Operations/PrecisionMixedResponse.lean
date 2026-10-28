module

public import GeneratedFoundations.Operations.FinitePrecisionTilt
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Mixed responses of one actual Gaussian precision comparison

The two insertions vary one and the same precision by `s*r+t*y`.
The logarithmic partition is the one-mode specialization of
`FinitePrecisionTilt.logPartition`, hence of its Gaussian integral.
The formulas below are connected to actual partial derivatives, rather
than being definitions of coefficients subsequently called responses.
-/

@[expose] public section
noncomputable section
open scoped Topology

namespace GeneratedFoundations.Operations.PrecisionMixedResponse

def precision (r y s t : ℝ) : ℝ := 1 + s * r + t * y

def logPartition (r y s t : ℝ) : ℝ := -Real.log (precision r y s t) / 2

theorem logPartition_eq_actual (r y s t : ℝ) :
    logPartition r y s t =
      FinitePrecisionTilt.logPartition (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => s * r + t * y) 1 := by
  simp [logPartition, precision, FinitePrecisionTilt.logPartition, add_assoc]

theorem actual_log_partition {r y s t : ℝ} (hp : 0 < precision r y s t) :
    Real.log (FinitePrecisionTilt.partition (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => s * r + t * y) 1) = logPartition r y s t := by
  rw [logPartition_eq_actual]
  apply FinitePrecisionTilt.log_partition (by intro i; norm_num)
  intro i
  simpa [FinitePrecisionTilt.variedPrecision, precision, add_assoc] using hp

def numerator (r y : ℝ) (k l : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + l) * ((k + l - 1).factorial : ℝ) / 2 * r ^ k * y ^ l

def positiveResponse (r y : ℝ) (k l : ℕ) (s t : ℝ) : ℝ :=
  numerator r y k l * precision r y s t ^ (-((k + l : ℕ) : ℤ))

/-- Order zero is the original log partition. Positive orders have the
factorial expression whose derivative recurrences are proved below. -/
def response (r y : ℝ) (k l : ℕ) (s t : ℝ) : ℝ :=
  if k + l = 0 then logPartition r y s t else positiveResponse r y k l s t

theorem response_zero (r y : ℝ) : response r y 0 0 = logPartition r y := by
  funext s t
  rfl

theorem response_of_ne (r y : ℝ) (k l : ℕ) (h : k + l ≠ 0) :
    response r y k l = positiveResponse r y k l := by
  funext s t
  simp only [response, h, ↓reduceIte]

theorem numerator_succ_left (r y : ℝ) (k l : ℕ) (h : k + l ≠ 0) :
    numerator r y (k + 1) l = -((k + l : ℕ) : ℝ) * r * numerator r y k l := by
  have hf : ((k + l).factorial : ℝ) =
      ((k + l : ℕ) : ℝ) * ((k + l - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred h).symm
  unfold numerator
  rw [show k + 1 + l = k + l + 1 by omega]
  simp only [Nat.add_sub_cancel, pow_succ, hf]
  ring

theorem numerator_succ_right (r y : ℝ) (k l : ℕ) (h : k + l ≠ 0) :
    numerator r y k (l + 1) = -((k + l : ℕ) : ℝ) * y * numerator r y k l := by
  have hf : ((k + l).factorial : ℝ) =
      ((k + l : ℕ) : ℝ) * ((k + l - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred h).symm
  unfold numerator
  rw [show k + (l + 1) = k + l + 1 by omega]
  simp only [Nat.add_sub_cancel, pow_succ, hf]
  ring

theorem positiveResponse_hasDerivAt_left (r y : ℝ) (k l : ℕ) (s t : ℝ)
    (hn : k + l ≠ 0) (hp : precision r y s t ≠ 0) :
    HasDerivAt (fun z => positiveResponse r y k l z t)
      (positiveResponse r y (k + 1) l s t) s := by
  have hd : HasDerivAt (fun z => precision r y z t) r s := by
    simpa [precision] using (((hasDerivAt_id s).mul_const r).const_add 1).add_const (t * y)
  have hz := ((hasDerivAt_zpow (-((k + l : ℕ) : ℤ))
    (precision r y s t) (Or.inl hp)).comp s hd).const_mul (numerator r y k l)
  convert hz using 1
  · rfl
  · unfold positiveResponse
    rw [numerator_succ_left r y k l hn]
    rw [show -((k + 1 + l : ℕ) : ℤ) = -((k + l : ℕ) : ℤ) - 1 by omega]
    simp only [Int.cast_neg, Int.cast_natCast]
    ring

theorem positiveResponse_hasDerivAt_right (r y : ℝ) (k l : ℕ) (s t : ℝ)
    (hn : k + l ≠ 0) (hp : precision r y s t ≠ 0) :
    HasDerivAt (positiveResponse r y k l s)
      (positiveResponse r y k (l + 1) s t) t := by
  have hd : HasDerivAt (precision r y s) y t := by
    convert (hasDerivAt_const t (1 + s * r)).add ((hasDerivAt_id t).mul_const y) using 1
    · rfl
    · ring
  have hz := ((hasDerivAt_zpow (-((k + l : ℕ) : ℤ))
    (precision r y s t) (Or.inl hp)).comp t hd).const_mul (numerator r y k l)
  convert hz using 1
  · rfl
  · unfold positiveResponse
    rw [numerator_succ_right r y k l hn]
    rw [show -((k + (l + 1) : ℕ) : ℤ) = -((k + l : ℕ) : ℤ) - 1 by omega]
    simp only [Int.cast_neg, Int.cast_natCast]
    ring

theorem logPartition_hasDerivAt_left (r y s t : ℝ) (hp : precision r y s t ≠ 0) :
    HasDerivAt (fun z => logPartition r y z t)
      (positiveResponse r y 1 0 s t) s := by
  have hd : HasDerivAt (fun z => precision r y z t) r s := by
    simpa [precision] using (((hasDerivAt_id s).mul_const r).const_add 1).add_const (t * y)
  have hz := (hd.log hp).neg.div_const 2
  convert hz using 1
  · rfl
  · simp [positiveResponse, numerator, zpow_neg, div_eq_mul_inv]
    ring

theorem logPartition_hasDerivAt_right (r y s t : ℝ) (hp : precision r y s t ≠ 0) :
    HasDerivAt (logPartition r y s)
      (positiveResponse r y 0 1 s t) t := by
  have hd : HasDerivAt (precision r y s) y t := by
    convert (hasDerivAt_const t (1 + s * r)).add ((hasDerivAt_id t).mul_const y) using 1
    · rfl
    · ring
  have hz := (hd.log hp).neg.div_const 2
  convert hz using 1
  · rfl
  · simp [positiveResponse, numerator, zpow_neg, div_eq_mul_inv]
    ring

theorem response_hasDerivAt_left (r y : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : precision r y s t ≠ 0) :
    HasDerivAt (fun z => response r y k l z t) (response r y (k + 1) l s t) s := by
  by_cases hn : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    rw [response_zero, response_of_ne r y 1 0 (by norm_num)]
    exact logPartition_hasDerivAt_left r y s t hp
  · rw [response_of_ne r y k l hn,
      response_of_ne r y (k + 1) l (by omega)]
    exact positiveResponse_hasDerivAt_left r y k l s t hn hp

theorem response_hasDerivAt_right (r y : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : precision r y s t ≠ 0) :
    HasDerivAt (response r y k l s) (response r y k (l + 1) s t) t := by
  by_cases hn : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    rw [response_zero, response_of_ne r y 0 1 (by norm_num)]
    exact logPartition_hasDerivAt_right r y s t hp
  · rw [response_of_ne r y k l hn,
      response_of_ne r y k (l + 1) (by omega)]
    exact positiveResponse_hasDerivAt_right r y k l s t hn hp

/-- All right partial derivatives are derivatives of the original log
partition on its nonsingular precision domain. -/
theorem iteratedDeriv_right (r y s : ℝ) (l : ℕ) (t : ℝ)
    (hp : precision r y s t ≠ 0) :
    iteratedDeriv l (logPartition r y s) t = response r y 0 l s t := by
  induction l generalizing t with
  | zero => simp only [iteratedDeriv_zero, response_zero]
  | succ l ih =>
    rw [iteratedDeriv_succ]
    have hc : Continuous (precision r y s) := by unfold precision; fun_prop
    have he : iteratedDeriv l (logPartition r y s) =ᶠ[nhds t] response r y 0 l s := by
      filter_upwards [hc.continuousAt.eventually (eventually_ne_nhds hp)] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_right r y 0 l s t hp).deriv

/-- The explicit response is the actual iterated mixed partial derivative.
The order displayed here first takes the right derivatives, then the left
derivatives; no interchange of limits or derivative orders is assumed. -/
theorem iteratedDeriv_mixed (r y : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : precision r y s t ≠ 0) :
    iteratedDeriv k (fun z => iteratedDeriv l (logPartition r y z) t) s =
      response r y k l s t := by
  induction k generalizing s with
  | zero =>
    simpa only [iteratedDeriv_zero] using iteratedDeriv_right r y s l t hp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hc : Continuous (fun z => precision r y z t) := by unfold precision; fun_prop
    have he :
        iteratedDeriv k (fun z => iteratedDeriv l (logPartition r y z) t) =ᶠ[nhds s]
          (fun z => response r y k l z t) := by
      filter_upwards [hc.continuousAt.eventually (eventually_ne_nhds hp)] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_left r y k l s t hp).deriv

theorem mixed_derivative_at_origin (r y : ℝ) (k l : ℕ) (hn : k + l ≠ 0) :
    iteratedDeriv k (fun s => iteratedDeriv l (logPartition r y s) 0) 0 =
      (-1 : ℝ) ^ (k + l) * ((k + l - 1).factorial : ℝ) / 2 * r ^ k * y ^ l := by
  rw [iteratedDeriv_mixed r y k l 0 0 (by norm_num [precision]),
    response_of_ne r y k l hn]
  simp [positiveResponse, precision, numerator]

/-- The product capacity is an actual higher mixed response of the same
Gaussian precision, with its sign and factorial normalization retained. -/
theorem capacity_power_mixed_derivative (r y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => iteratedDeriv n (logPartition r y s) 0) 0 =
      (-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2 * (y * r ^ 2) ^ n := by
  rw [mixed_derivative_at_origin r y (2 * n) n (by omega)]
  rw [show 2 * n + n = 3 * n by omega, mul_pow, pow_mul]
  ring

theorem split_capacity_power_mixed_derivative (y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n (logPartition (1 - y) y s) 0) 0 =
      (-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2 *
        (y * (1 - y) ^ 2) ^ n :=
  capacity_power_mixed_derivative (1 - y) y n hn

/-- The same identity stated directly in the original Gaussian tilt API. -/
theorem actual_capacity_power_mixed_derivative (r y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => iteratedDeriv n
      (fun t => FinitePrecisionTilt.logPartition (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => s * r + t * y) 1) 0) 0 =
      (-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2 * (y * r ^ 2) ^ n := by
  simp_rw [← logPartition_eq_actual]
  exact capacity_power_mixed_derivative r y n hn

/-- The same comparison in the original Gaussian variable and precision.
Both insertions act on that variable before integration; the ratios enter
only after evaluating the actual partition. -/
theorem original_precision_log_partition {A b s t : ℝ}
    (hp : 0 < A + b) (hv : 0 < A + b + s * A + t * b) :
    Real.log (∫ x : ℝ, Real.exp (-(s * A + t * b) * x ^ 2 / 2)
      ∂GaussianPrecisionKL.law (A + b)) =
      logPartition (A / (A + b)) (b / (A + b)) s t := by
  have hv' : 0 < A + b + 1 * (s * A + t * b) := by linarith
  have he := FinitePrecisionTilt.scalar_partition
    (p := A + b) (q := s * A + t * b) (z := 1) hp hv'
  have hi : (fun x : ℝ => Real.exp (-(s * A + t * b) * x ^ 2 / 2)) =
      (fun x : ℝ => Real.exp (-1 * ((s * A + t * b) / 2 * x ^ 2))) := by
    funext x
    congr 1
    ring
  rw [hi, he, Real.log_exp]
  have hr : precision (A / (A + b)) (b / (A + b)) s t =
      (A + b + 1 * (s * A + t * b)) / (A + b) := by
    unfold precision
    field_simp [hp.ne']
    ring
  rw [logPartition, hr, Real.log_div hp.ne' hv'.ne', Real.log_div hv'.ne' hp.ne']
  ring

theorem original_kinetic_fraction {A b : ℝ} (hp : A + b ≠ 0) :
    A / (A + b) = 1 - b / (A + b) := by
  field_simp
  ring

/-- Specializing the original precision gives exactly the split comparison
used in the mixed-capacity theorem. -/
theorem original_precision_split_log_partition {A b s t : ℝ}
    (hp : 0 < A + b) (hv : 0 < A + b + s * A + t * b) :
    Real.log (∫ x : ℝ, Real.exp (-(s * A + t * b) * x ^ 2 / 2)
      ∂GaussianPrecisionKL.law (A + b)) =
      logPartition (1 - b / (A + b)) (b / (A + b)) s t := by
  rw [original_precision_log_partition hp hv, original_kinetic_fraction hp.ne']

end GeneratedFoundations.Operations.PrecisionMixedResponse
