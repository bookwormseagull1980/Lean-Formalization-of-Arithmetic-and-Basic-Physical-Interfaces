module

public import GeneratedFoundations.Physical.SourceTTCollectiveVariance
public import GeneratedFoundations.Operations.PrecisionMixedResponse

/-!
# Transport of TT comparison moments under the existing mass variation

The logarithmic mass parameter is the one already used in the retained
source precision. Differentiating its comparison readouts gives a coupled
moment hierarchy. Multiplication by the capacity is a different operation:
its powers are comparison moments, not iterates of this mass derivative.
The propagator factorization below identifies the elementary response
whose products enter those moments; it does not prescribe a source update.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceTTComparisonTransport

open SourceTensorResponseEndpoint SourceTTCollectiveComparison
  SourceTTCollectiveVariance

def capacity (a b z u : ℝ) : ℝ :=
  massWeightedResponse (fraction a b z u)

theorem capacity_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) :
    HasDerivAt (fun t => capacity a b t u)
      (capacity a b z u * (1 - 3 * fraction a b z u)) z := by
  have hf := fraction_hasDerivAt ha hb z u
  convert! hf.mul (((hasDerivAt_const z (1 : ℝ)).sub hf).pow 2) using 1
  unfold capacity massWeightedResponse
  simp only [Pi.pow_apply, Pi.sub_apply]
  ring

theorem fraction_pow_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) (k : ℕ) :
    HasDerivAt (fun t => fraction a b t u ^ k)
      ((k : ℝ) * fraction a b z u ^ k * (1 - fraction a b z u)) z := by
  cases k with
  | zero => simpa using hasDerivAt_const z (1 : ℝ)
  | succ k =>
    convert! (fraction_hasDerivAt ha hb z u).pow (k + 1) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem capacity_pow_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) (n : ℕ) :
    HasDerivAt (fun t => capacity a b t u ^ n)
      ((n : ℝ) * capacity a b z u ^ n * (1 - 3 * fraction a b z u)) z := by
  cases n with
  | zero => simpa using hasDerivAt_const z (1 : ℝ)
  | succ n =>
    convert! (capacity_hasDerivAt ha hb z u).pow (n + 1) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- The Gaussian envelope, branch and frequency remain those of the
original trace. Both exponents index observables, not physical times. -/
def momentProfile (n k : ℕ) (a b z u : ℝ) : ℝ :=
  fraction a b z u ^ k * capacity a b z u ^ n * envelope a u

/-- Exact local hierarchy for the existing logarithmic mass variation:
`H[n,k]' = (k+n) H[n,k] - (k+3n) H[n,k+1]`.
No closure by a single effective mass fraction is used. -/
theorem momentProfile_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) (n k : ℕ) :
    HasDerivAt (fun t => momentProfile n k a b t u)
      (((k : ℝ) + n) * momentProfile n k a b z u -
        ((k : ℝ) + 3 * n) * momentProfile n (k + 1) a b z u) z := by
  convert! ((fraction_pow_hasDerivAt ha hb z u k).mul
    (capacity_pow_hasDerivAt ha hb z u n)).mul_const (envelope a u) using 1
  unfold momentProfile
  rw [pow_succ]
  ring

/-- The same hierarchy holds for any retained finite quadrature, with
all its original weights included. -/
theorem finite_moment_hasDerivAt {ι : Type*} (s : Finset ι)
    (a b u w : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 < b i) (z : ℝ) (n k : ℕ) :
    HasDerivAt
      (fun t => ∑ i ∈ s, w i * momentProfile n k (a i) (b i) t (u i))
      (((k : ℝ) + n) * (∑ i ∈ s, w i * momentProfile n k (a i) (b i) z (u i)) -
        ((k : ℝ) + 3 * n) *
          (∑ i ∈ s, w i * momentProfile n (k + 1) (a i) (b i) z (u i))) z := by
  convert! HasDerivAt.fun_sum (u := s) (fun i hi =>
    (momentProfile_hasDerivAt (ha i hi) (hb i hi) z (u i) n k).const_mul (w i)) using 1
  simp_rw [mul_sub, ← mul_assoc, mul_comm (w _) ((_ : ℝ) + _)]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem momentProfile_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z : ℝ) (n k : ℕ) : Continuous (momentProfile n k a b z) := by
  have hc : Continuous (capacity a b z) := by
    unfold capacity massWeightedResponse
    exact (fraction_continuous ha hb z).mul
      ((continuous_const.sub (fraction_continuous ha hb z)).pow 2)
  exact ((fraction_continuous ha hb z).pow k).mul (hc.pow n) |>.mul
    (show Continuous (envelope a) by unfold envelope; fun_prop)

theorem momentProfile_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) (n k : ℕ) :
    0 ≤ momentProfile n k a b z u ∧ momentProfile n k a b z u ≤ envelope a u := by
  have hy := fraction_bounds ha hb z u
  have hc0 : 0 ≤ capacity a b z u := by
    unfold capacity massWeightedResponse
    exact mul_nonneg hy.1 (sq_nonneg _)
  have hc1 : capacity a b z u ≤ 1 :=
    (massWeightedResponse_le hy.1 hy.2).trans (by norm_num)
  have hprod0 := mul_nonneg (pow_nonneg hy.1 k) (pow_nonneg hc0 n)
  have hprod1 : fraction a b z u ^ k * capacity a b z u ^ n ≤ 1 := by
    simpa using mul_le_mul (pow_le_one₀ hy.1 hy.2) (pow_le_one₀ hc0 hc1)
      (pow_nonneg hc0 n) (by norm_num : (0 : ℝ) ≤ 1)
  have he : 0 ≤ envelope a u := (Real.exp_pos _).le
  exact ⟨mul_nonneg hprod0 he,
    (mul_le_mul_of_nonneg_right hprod1 he).trans_eq (one_mul _)⟩

/-- Differentiation of the full frequency integral is justified with a
bound in the original Gaussian envelope, uniform in the mass parameter. -/
theorem frequency_moment_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z v : ℝ) (n k : ℕ) :
    HasDerivAt (fun t => ∫ u in (0 : ℝ)..v, momentProfile n k a b t u)
      (((k : ℝ) + n) * (∫ u in (0 : ℝ)..v, momentProfile n k a b z u) -
        ((k : ℝ) + 3 * n) *
          (∫ u in (0 : ℝ)..v, momentProfile n (k + 1) a b z u)) z := by
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := v)
    (F := fun t u => momentProfile n k a b t u)
    (F' := fun t u => ((k : ℝ) + n) * momentProfile n k a b t u -
      ((k : ℝ) + 3 * n) * momentProfile n (k + 1) a b t u)
    (bound := fun u => (2 * (k : ℝ) + 4 * n) * envelope a u)
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ nhds z)
    (Filter.Eventually.of_forall fun t =>
      (momentProfile_continuous ha hb t n k).aestronglyMeasurable)
    ((momentProfile_continuous ha hb z n k).intervalIntegrable _ _)
    (((continuous_const.mul (momentProfile_continuous ha hb z n k)).sub
      (continuous_const.mul (momentProfile_continuous ha hb z n (k + 1)))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u _ t _ => by
      have hm := momentProfile_bounds ha hb t u n k
      have hn := momentProfile_bounds ha hb t u n (k + 1)
      have hm1 := mul_le_mul_of_nonneg_left hm.2
        (by positivity : 0 ≤ (k : ℝ) + n)
      have hn1 := mul_le_mul_of_nonneg_left hn.2
        (by positivity : 0 ≤ (k : ℝ) + 3 * n)
      have hm0 : 0 ≤ ((k : ℝ) + n) * momentProfile n k a b t u :=
        mul_nonneg (by positivity) hm.1
      have hn0 : 0 ≤ ((k : ℝ) + 3 * n) * momentProfile n (k + 1) a b t u :=
        mul_nonneg (by positivity) hn.1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith)
    ((by unfold envelope; fun_prop : Continuous
      (fun u => (2 * (k : ℝ) + 4 * n) * envelope a u)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun u _ t _ => momentProfile_hasDerivAt ha hb t u n k)).2
  convert! hd using 1
  rw [intervalIntegral.integral_sub
    (f := fun u => ((k : ℝ) + n) * momentProfile n k a b z u)
    (g := fun u => ((k : ℝ) + 3 * n) * momentProfile n (k + 1) a b z u)
    ((continuous_const.mul (momentProfile_continuous ha hb z n k)).intervalIntegrable _ _)
    ((continuous_const.mul (momentProfile_continuous ha hb z n (k + 1))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

def traceMoment (n k : ℕ) (z : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) * ∑ i : Branch,
    (SourceTTGaussianCoefficient.branch i).2.2 *
      ∫ u in (0 : ℝ)..upper i,
        momentProfile n k (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u

/-- The hierarchy on the actual eight retained branches and their fixed
frequency integrals; no quadrature replaces the source trace. -/
theorem traceMoment_hasDerivAt (n k : ℕ) (z : ℝ) :
    HasDerivAt (traceMoment n k)
      (((k : ℝ) + n) * traceMoment n k z -
        ((k : ℝ) + 3 * n) * traceMoment n (k + 1) z) z := by
  have hi (i : Branch) :=
    (frequency_moment_hasDerivAt (SourceTTGaussianCoefficient.branch_bounds i).1
      (SourceTTGaussianCoefficient.branch_bounds i).2.2.1 z (upper i) n k).const_mul
        (SourceTTGaussianCoefficient.branch i).2.2
  convert! (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i).const_mul
    (1 / (32 * Real.pi ^ 3)) using 1
  simp only [traceMoment, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Connected mixed response of the same normalized precision, evaluated
before the original frequency envelope is applied. -/
def connectedProfile (n : ℕ) (a b z u : ℝ) : ℝ :=
  envelope a u * iteratedDeriv (2 * n)
    (fun s => iteratedDeriv n
      (Operations.PrecisionMixedResponse.logPartition
        (1 - fraction a b z u) (fraction a b z u) s) 0) 0

theorem connectedProfile_eq (n : ℕ) (hn : 1 ≤ n) (a b z u : ℝ) :
    connectedProfile n a b z u =
      ((-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2) *
        momentProfile n 0 a b z u := by
  unfold connectedProfile
  rw [Operations.PrecisionMixedResponse.split_capacity_power_mixed_derivative _ n hn]
  simp only [momentProfile, pow_zero, one_mul, capacity, massWeightedResponse]
  ring

/-- A weighted trace of actual one-mode log-partition derivatives.
The continuous envelope is a trace weight, not a number of Gaussian
copies in a new global probability measure. -/
def connectedTrace (n : ℕ) (z : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) * ∑ i : Branch,
    (SourceTTGaussianCoefficient.branch i).2.2 *
      ∫ u in (0 : ℝ)..upper i,
        connectedProfile n (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u

/-- All product moments in the original eight-branch trace are normalized
higher connected responses of the same precision comparison. -/
theorem connectedTrace_eq (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    connectedTrace n z =
      ((-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2) * traceMoment n 0 z := by
  unfold connectedTrace traceMoment
  simp_rw [connectedProfile_eq n hn, intervalIntegral.integral_const_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def normalizedConnectedTrace (n : ℕ) (z : ℝ) : ℝ :=
  connectedTrace n z /
    ((-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2)

theorem normalizedConnectedTrace_eq (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    normalizedConnectedTrace n z = traceMoment n 0 z := by
  have hc : ((-1 : ℝ) ^ (3 * n) * ((3 * n - 1).factorial : ℝ) / 2) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) (by norm_num)
  unfold normalizedConnectedTrace
  rw [connectedTrace_eq n hn z]
  exact mul_div_cancel_left₀ _ hc

/-- The adjacent moment comparison can be read directly from successive
connected responses of the original source, with the Gaussian factorial
normalization fixed by differentiation. -/
theorem connected_ratio_eq_moment_ratio (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    normalizedConnectedTrace (n + 1) z / normalizedConnectedTrace n z =
      traceMoment (n + 1) 0 z / traceMoment n 0 z := by
  rw [normalizedConnectedTrace_eq (n + 1) (by omega) z,
    normalizedConnectedTrace_eq n hn z]

def transportDenominator (y h : ℝ) : ℝ := 1 + (Real.exp h - 1) * y

theorem transportDenominator_pos {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (h : ℝ) :
    0 < transportDenominator y h := by
  by_cases hy : y = 0
  · simp [transportDenominator, hy]
  · have hp := mul_pos (Real.exp_pos h) (lt_of_le_of_ne hy0 (Ne.symm hy))
    unfold transportDenominator
    nlinarith

/-- Finite transport induced by `b ↦ exp(h) b` in the actual precision.
It is a rational transport of mass fractions, rather than multiplication
by the TT capacity. -/
theorem fraction_finite_transport {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z h u : ℝ) :
    fraction a b (z + h) u =
      Real.exp h * fraction a b z u /
        transportDenominator (fraction a b z u) h := by
  have hy := fraction_bounds ha hb z u
  have hd := (transportDenominator_pos hy.1 hy.2 h).ne'
  have hp : u ^ 2 + a + Real.exp z * b ≠ 0 := by
    have hm := mul_pos (Real.exp_pos z) hb
    nlinarith [sq_nonneg u]
  have hq : u ^ 2 + a + Real.exp (z + h) * b ≠ 0 := by
    have hm := mul_pos (Real.exp_pos (z + h)) hb
    nlinarith [sq_nonneg u]
  apply (div_eq_div_iff hq hd).2
  unfold transportDenominator fraction massFraction
  rw [Real.exp_add]
  field_simp [hp]
  ring

theorem capacity_finite_transport {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z h u : ℝ) :
    capacity a b (z + h) u =
      Real.exp h * capacity a b z u /
        transportDenominator (fraction a b z u) h ^ 3 := by
  have hy := fraction_bounds ha hb z u
  have hd := (transportDenominator_pos hy.1 hy.2 h).ne'
  unfold capacity
  rw [fraction_finite_transport ha hb z h u]
  let d := transportDenominator (fraction a b z u) h
  have hdn : d ≠ 0 := hd
  change massWeightedResponse (Real.exp h * fraction a b z u / d) =
    Real.exp h * massWeightedResponse (fraction a b z u) / d ^ 3
  unfold massWeightedResponse
  field_simp [hdn]
  dsimp [d, transportDenominator]
  ring

/-- Exact finite transport for every product readout. The denominator
records the simultaneous change of the original source precision. -/
theorem momentProfile_finite_transport {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z h u : ℝ) (n k : ℕ) :
    momentProfile n k a b (z + h) u =
      (Real.exp h / transportDenominator (fraction a b z u) h) ^ k *
        (Real.exp h / transportDenominator (fraction a b z u) h ^ 3) ^ n *
          momentProfile n k a b z u := by
  unfold momentProfile
  rw [fraction_finite_transport ha hb z h u, capacity_finite_transport ha hb z h u]
  simp only [div_eq_mul_inv, mul_pow]
  ring

/-- Two kinetic insertions and three propagators, with the same mass
insertion as in the precision comparison. This is an exact response
factorization, not an identification with a Mehler transition kernel. -/
theorem capacity_propagator_factorization {A m : ℝ} (hp : A + m ≠ 0) :
    massWeightedResponse (massFraction A m) =
      m * (A + m)⁻¹ * A * (A + m)⁻¹ * A * (A + m)⁻¹ := by
  unfold massWeightedResponse massFraction
  field_simp
  ring

theorem capacity_stationary_at_peak {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) (hy : fraction a b z u = 1 / 3) :
    HasDerivAt (fun t => capacity a b t u) 0 z := by
  simpa [hy] using capacity_hasDerivAt ha hb z u

/-- At the actual capacity maximum, the mass derivative is zero whereas
the next product moment is positive. Thus the two local operations
cannot be identified. -/
theorem mass_derivative_ne_capacity_product_at_peak {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ)
    (hy : fraction a b z u = 1 / 3) :
    ¬ HasDerivAt (fun t => capacity a b t u) (capacity a b z u ^ 2) z := by
  intro h
  have he := (capacity_stationary_at_peak ha hb z u hy).unique h
  norm_num [capacity, massWeightedResponse, hy] at he

end GeneratedFoundations.Physical.SourceTTComparisonTransport
