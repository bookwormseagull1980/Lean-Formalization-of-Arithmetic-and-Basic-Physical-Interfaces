module

public import GeneratedFoundations.Physical.SourceTTFrameComparison
public import GeneratedFoundations.Operations.PrecisionMixedResponse

/-!
# Connected responses of the actual unit-plus tensor vertex

The first precision vertex has eigenvalues `-4,4,0` on each of the three
real adjoint rows. Both signs, the passive coordinate, and the original
nine-coordinate Gaussian law are retained. The mixed responses below are
actual derivatives of this law's logarithmic partition for linear precision
insertions. The direct second vertex of a nonlinear frame path remains the
separate term proved in `SourceTTFrameComparison`.

The capacity powers follow by comparison with the pure-kinetic response of
the same tensor vertex at each order. Its six active coordinates and vertex
moments cancel in the ratio. This introduces no new evolution or vertex
normalization.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace GeneratedFoundations.Physical.SourceTTTensorConnectedResponse

open SourceTTFrameComparison
open Operations


abbrev Coord := Fin 3 × Fin 3

def plusEigenvalue (i : Fin 3) : ℝ := ![-4, 4, 0] i

def vertexCoefficients (i : Coord) : ℝ := plusEigenvalue i.1

theorem actual_plus_vertex :
    repeatRows (vertex (Geometry.SourceAxisTT.ttMatrix 1 0)) =
      Matrix.diagonal vertexCoefficients := by
  rw [tt_vertex]
  ext i j
  rcases i with ⟨i, r⟩
  rcases j with ⟨j, t⟩
  fin_cases i <;> fin_cases j <;>
    simp [repeatRows, Matrix.blockDiagonal_apply, Matrix.diagonal,
      Geometry.SourceAxisTT.ttMatrix, vertexCoefficients, plusEigenvalue,
      Prod.ext_iff]

theorem original_law_eq {p : ℝ} (hp : 0 < p) :
    FiniteMatrixGaussian.law (repeatRows (precision p)) =
      FinitePrecisionGaussian.law (fun _ : Coord => p) := by
  unfold FiniteMatrixGaussian.law
  rw [repeated_inverse hp, precision_inverse]
  change multivariateGaussian 0 (repeatRows (precision p⁻¹)) = _
  rw [repeated_precision]
  rfl

def insertion (b s t : ℝ) (i : Coord) : ℝ :=
  s * vertexCoefficients i + t * b

theorem original_insertion (b s t : ℝ) :
    s • repeatRows (vertex (Geometry.SourceAxisTT.ttMatrix 1 0)) +
      (t * b) • (1 : Matrix Coord Coord ℝ) = Matrix.diagonal (insertion b s t) := by
  rw [actual_plus_vertex]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [insertion]
  · simp [Matrix.diagonal, hij]

def logPartition (p b s t : ℝ) : ℝ :=
  3 * (PrecisionMixedResponse.logPartition (-4 / p) (b / p) s t +
    PrecisionMixedResponse.logPartition (4 / p) (b / p) s t +
    PrecisionMixedResponse.logPartition 0 (b / p) s t)

def actualPartition (p b s t : ℝ) : ℝ :=
  ∫ x, Real.exp (-FiniteMatrixGaussian.score
    (s • repeatRows (vertex (Geometry.SourceAxisTT.ttMatrix 1 0)) +
      (t * b) • (1 : Matrix Coord Coord ℝ)) x)
    ∂FiniteMatrixGaussian.law (repeatRows (precision p))

theorem logPartition_eq_diagonal (p b s t : ℝ) :
    FinitePrecisionTilt.logPartition (fun _ : Coord => p) (insertion b s t) 1 =
      logPartition p b s t := by
  simp [FinitePrecisionTilt.logPartition, insertion, vertexCoefficients,
    plusEigenvalue, logPartition, PrecisionMixedResponse.logPartition, PrecisionMixedResponse.precision,
    Fintype.sum_prod_type, Fin.sum_univ_three, add_div, mul_div_assoc]
  ring_nf

/-- The partition is evaluated in the same original nine-coordinate law
used for the tensor covariance and direct frame response. -/
theorem actual_log_partition {p b s t : ℝ} (hp : 0 < p)
    (hv : ∀ i : Coord, 0 < p + insertion b s t i) :
    Real.log (actualPartition p b s t) = logPartition p b s t := by
  have he : actualPartition p b s t =
      FinitePrecisionTilt.partition (fun _ : Coord => p) (insertion b s t) 1 := by
    rw [actualPartition, original_insertion, original_law_eq hp]
    congr 1
    funext x
    simp [FiniteMatrixGaussian.score, FinitePrecisionGaussian.score,
      GaussianPrecisionMoments.score, Matrix.diagonal, ite_div, ite_mul, pow_two]
  rw [he, FinitePrecisionTilt.log_partition (fun _ => hp)
    (by simpa [FinitePrecisionTilt.variedPrecision] using hv)]
  exact logPartition_eq_diagonal p b s t

theorem actual_right_derivative_eq {p b s : ℝ} (hp : 0 < p)
    (hv : ∀ i : Coord, 0 < p + insertion b s 0 i) (l : ℕ) :
    iteratedDeriv l (fun t => Real.log (actualPartition p b s t)) 0 =
      iteratedDeriv l (logPartition p b s) 0 := by
  have hc (i : Coord) : Continuous (fun t => p + insertion b s t i) := by
    unfold insertion
    fun_prop
  have hepos : ∀ᶠ t in nhds (0 : ℝ), ∀ i : Coord, 0 < p + insertion b s t i :=
    Filter.eventually_all.mpr fun i =>
      (isOpen_lt continuous_const (hc i)).mem_nhds (hv i)
  have he : (fun t => Real.log (actualPartition p b s t)) =ᶠ[nhds 0]
      logPartition p b s := by
    filter_upwards [hepos] with t ht
    exact actual_log_partition hp ht
  exact he.iteratedDeriv_eq l

/-- Equality of mixed derivatives transfers through the actual partition
on an open positive-precision neighbourhood, at every finite order. -/
theorem actual_mixed_derivative_eq {p b : ℝ} (hp : 0 < p) (k l : ℕ) :
    iteratedDeriv k
        (fun s => iteratedDeriv l (fun t => Real.log (actualPartition p b s t)) 0) 0 =
      iteratedDeriv k (fun s => iteratedDeriv l (logPartition p b s) 0) 0 := by
  have hc (i : Coord) : Continuous (fun s => p + insertion b s 0 i) := by
    unfold insertion
    fun_prop
  have hepos : ∀ᶠ s in nhds (0 : ℝ), ∀ i : Coord, 0 < p + insertion b s 0 i :=
    Filter.eventually_all.mpr fun i =>
      (isOpen_lt continuous_const (hc i)).mem_nhds (by simpa [insertion] using hp)
  have he :
      (fun s => iteratedDeriv l (fun t => Real.log (actualPartition p b s t)) 0)
        =ᶠ[nhds 0] (fun s => iteratedDeriv l (logPartition p b s) 0) := by
    filter_upwards [hepos] with s hs
    exact actual_right_derivative_eq hp hs l
  exact he.iteratedDeriv_eq k

def response (p b : ℝ) (k l : ℕ) (s t : ℝ) : ℝ :=
  3 * (PrecisionMixedResponse.response (-4 / p) (b / p) k l s t +
    PrecisionMixedResponse.response (4 / p) (b / p) k l s t +
    PrecisionMixedResponse.response 0 (b / p) k l s t)

def Nonsingular (p b s t : ℝ) : Prop :=
  PrecisionMixedResponse.precision (-4 / p) (b / p) s t ≠ 0 ∧
  PrecisionMixedResponse.precision (4 / p) (b / p) s t ≠ 0 ∧
  PrecisionMixedResponse.precision 0 (b / p) s t ≠ 0

theorem response_zero (p b : ℝ) : response p b 0 0 = logPartition p b := by
  funext s t
  simp [response, PrecisionMixedResponse.response_zero, logPartition]

theorem response_hasDerivAt_left (p b : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : Nonsingular p b s t) :
    HasDerivAt (fun z => response p b k l z t)
      (response p b (k + 1) l s t) s := by
  exact (((PrecisionMixedResponse.response_hasDerivAt_left _ _ k l s t hp.1).add
    (PrecisionMixedResponse.response_hasDerivAt_left _ _ k l s t hp.2.1)).add
    (PrecisionMixedResponse.response_hasDerivAt_left _ _ k l s t hp.2.2)).const_mul 3

theorem response_hasDerivAt_right (p b : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : Nonsingular p b s t) :
    HasDerivAt (response p b k l s)
      (response p b k (l + 1) s t) t := by
  exact (((PrecisionMixedResponse.response_hasDerivAt_right _ _ k l s t hp.1).add
    (PrecisionMixedResponse.response_hasDerivAt_right _ _ k l s t hp.2.1)).add
    (PrecisionMixedResponse.response_hasDerivAt_right _ _ k l s t hp.2.2)).const_mul 3

theorem nonsingular_eventually_right {p b s t : ℝ} (hp : Nonsingular p b s t) :
    ∀ᶠ z in nhds t, Nonsingular p b s z := by
  have hc (r : ℝ) : Continuous (PrecisionMixedResponse.precision r (b / p) s) := by
    unfold PrecisionMixedResponse.precision
    fun_prop
  filter_upwards [(hc (-4 / p)).continuousAt.eventually (eventually_ne_nhds hp.1),
    (hc (4 / p)).continuousAt.eventually (eventually_ne_nhds hp.2.1),
    (hc 0).continuousAt.eventually (eventually_ne_nhds hp.2.2)] with z h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem nonsingular_eventually_left {p b s t : ℝ} (hp : Nonsingular p b s t) :
    ∀ᶠ z in nhds s, Nonsingular p b z t := by
  have hc (r : ℝ) : Continuous (fun z => PrecisionMixedResponse.precision r (b / p) z t) := by
    unfold PrecisionMixedResponse.precision
    fun_prop
  filter_upwards [(hc (-4 / p)).continuousAt.eventually (eventually_ne_nhds hp.1),
    (hc (4 / p)).continuousAt.eventually (eventually_ne_nhds hp.2.1),
    (hc 0).continuousAt.eventually (eventually_ne_nhds hp.2.2)] with z h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem iteratedDeriv_right (p b s : ℝ) (l : ℕ) (t : ℝ)
    (hp : Nonsingular p b s t) :
    iteratedDeriv l (logPartition p b s) t = response p b 0 l s t := by
  induction l generalizing t with
  | zero => simp only [iteratedDeriv_zero, response_zero]
  | succ l ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv l (logPartition p b s) =ᶠ[nhds t] response p b 0 l s := by
      filter_upwards [nonsingular_eventually_right hp] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_right p b 0 l s t hp).deriv

theorem iteratedDeriv_mixed (p b : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : Nonsingular p b s t) :
    iteratedDeriv k (fun z => iteratedDeriv l (logPartition p b z) t) s =
      response p b k l s t := by
  induction k generalizing s with
  | zero => simpa only [iteratedDeriv_zero] using iteratedDeriv_right p b s l t hp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he :
        iteratedDeriv k (fun z => iteratedDeriv l (logPartition p b z) t) =ᶠ[nhds s]
          (fun z => response p b k l z t) := by
      filter_upwards [nonsingular_eventually_left hp] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_left p b k l s t hp).deriv

def gaussianDerivativeCoefficient (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((k - 1).factorial : ℝ) / 2

theorem gaussianDerivativeCoefficient_ne_zero (k : ℕ) :
    gaussianDerivativeCoefficient k ≠ 0 := by
  unfold gaussianDerivativeCoefficient
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast (Nat.factorial_ne_zero (k - 1)))) (by norm_num)

theorem vertex_even_moment (n : ℕ) (hn : 1 ≤ n) :
    (∑ i : Coord, vertexCoefficients i ^ (2 * n)) = 6 * 16 ^ n := by
  simp [vertexCoefficients, plusEigenvalue, Fintype.sum_prod_type,
    Fin.sum_univ_three, show n ≠ 0 by omega, pow_mul]
  ring

theorem ratio_power (v p b : ℝ) (n : ℕ) :
    (v / p) ^ (2 * n) * (b / p) ^ n = (v ^ 2 * b / p ^ 3) ^ n := by
  rw [pow_mul, ← mul_pow]
  congr 1
  by_cases hp : p = 0
  · simp [hp]
  · field_simp

/-- All six active real coordinates contribute to every positive mixed
order; the three passive coordinates still occur in the partition. -/
theorem mixed_connected_derivative (p b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => iteratedDeriv n (logPartition p b s) 0) 0 =
      6 * gaussianDerivativeCoefficient (3 * n) * (16 * b / p ^ 3) ^ n := by
  rw [iteratedDeriv_mixed p b (2 * n) n 0 0 (by norm_num [Nonsingular, PrecisionMixedResponse.precision])]
  have hr (v : ℝ) : PrecisionMixedResponse.response (v / p) (b / p)
      (2 * n) n 0 0 =
      gaussianDerivativeCoefficient (3 * n) * (v ^ 2 * b / p ^ 3) ^ n := by
    rw [PrecisionMixedResponse.response_of_ne _ _ _ _ (by omega)]
    simp only [PrecisionMixedResponse.positiveResponse, PrecisionMixedResponse.precision,
      zero_mul, add_zero, one_zpow, mul_one, PrecisionMixedResponse.numerator]
    rw [show 2 * n + n = 3 * n by omega, ← ratio_power]
    unfold gaussianDerivativeCoefficient
    ring
  simp only [response]
  have hz := hr 0
  simp only [zero_div] at hz
  rw [hr (-4), hr 4, hz]
  norm_num [show n ≠ 0 by omega]
  ring

theorem actual_mixed_connected_derivative {p b : ℝ} (hp : 0 < p)
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n (fun t => Real.log (actualPartition p b s t)) 0) 0 =
      6 * gaussianDerivativeCoefficient (3 * n) * (16 * b / p ^ 3) ^ n := by
  rw [actual_mixed_derivative_eq hp]
  exact mixed_connected_derivative p b n hn

/-- The reference is the same tensor vertex with the mass insertion
absent, at the unshifted kinetic precision. -/
theorem pure_kinetic_connected_derivative (A : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => logPartition A 0 s 0) 0 =
      6 * gaussianDerivativeCoefficient (2 * n) * (16 / A ^ 2) ^ n := by
  have he := iteratedDeriv_mixed A 0 (2 * n) 0 0 0
    (by norm_num [Nonsingular, PrecisionMixedResponse.precision])
  simp only [iteratedDeriv_zero] at he
  rw [he]
  have hr (v : ℝ) : PrecisionMixedResponse.response (v / A) 0 (2 * n) 0 0 0 =
      gaussianDerivativeCoefficient (2 * n) * (v ^ 2 / A ^ 2) ^ n := by
    rw [PrecisionMixedResponse.response_of_ne _ _ _ _ (by omega)]
    simp only [PrecisionMixedResponse.positiveResponse, PrecisionMixedResponse.precision,
      mul_zero, zero_mul, add_zero, one_zpow, mul_one,
      PrecisionMixedResponse.numerator, pow_zero]
    have hv : (v / A) ^ (2 * n) = (v ^ 2 / A ^ 2) ^ n := by
      rw [pow_mul, div_pow]
    rw [hv]
    unfold gaussianDerivativeCoefficient
    rfl
  simp only [response, zero_div]
  have hz := hr 0
  simp only [zero_div] at hz
  rw [hr (-4), hr 4, hz]
  norm_num [show n ≠ 0 by omega]
  ring

theorem actual_pure_kinetic_connected_derivative {A : ℝ} (hA : 0 < A)
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => Real.log (actualPartition A 0 s 0)) 0 =
      6 * gaussianDerivativeCoefficient (2 * n) * (16 / A ^ 2) ^ n := by
  have he := actual_mixed_derivative_eq (b := 0) hA (2 * n) 0
  simp only [iteratedDeriv_zero] at he
  rw [he]
  exact pure_kinetic_connected_derivative A n hn

def capacity (A b : ℝ) : ℝ := b * A ^ 2 / (A + b) ^ 3

theorem capacity_eq_split {A b : ℝ} (hp : A + b ≠ 0) :
    capacity A b = (b / (A + b)) * (1 - b / (A + b)) ^ 2 := by
  unfold capacity
  field_simp
  ring

/-- An explicit frequency conversion, not a replacement of the physical
vertex: each order carries the factor `(A²/16)^n`. -/
theorem frequency_conversion (A b : ℝ) (n : ℕ) :
    (A ^ 2 / 16) ^ n * (16 * b / (A + b) ^ 3) ^ n = capacity A b ^ n := by
  rw [← mul_pow]
  congr 1
  unfold capacity
  ring

/-- Dividing each actual derivative by its Gaussian factorial coefficient
and comparing with the same vertex's pure-kinetic reference gives exactly
the capacity power. The six active coordinates cancel, rather than being
discarded or interpreted as independent copies of a scalar comparison. -/
theorem same_vertex_reference_ratio {A b : ℝ} (hA : 0 < A)
    (hp : 0 < A + b) (n : ℕ) (hn : 1 ≤ n) :
    ((iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n (logPartition (A + b) b s) 0) 0) /
      gaussianDerivativeCoefficient (3 * n)) /
      ((iteratedDeriv (2 * n) (fun s => logPartition A 0 s 0) 0) /
        gaussianDerivativeCoefficient (2 * n)) = capacity A b ^ n := by
  rw [mixed_connected_derivative _ _ n hn,
    pure_kinetic_connected_derivative A n hn]
  have hc3 := gaussianDerivativeCoefficient_ne_zero (3 * n)
  have hc2 := gaussianDerivativeCoefficient_ne_zero (2 * n)
  have hn3 (x : ℝ) : 6 * gaussianDerivativeCoefficient (3 * n) * x /
      gaussianDerivativeCoefficient (3 * n) = 6 * x := by
    field_simp
  have hn2 (x : ℝ) : 6 * gaussianDerivativeCoefficient (2 * n) * x /
      gaussianDerivativeCoefficient (2 * n) = 6 * x := by
    field_simp
  rw [hn3, hn2, mul_div_mul_left _ _ (by norm_num : (6 : ℝ) ≠ 0), ← div_pow]
  congr 1
  unfold capacity
  field_simp [hp.ne', hA.ne']

/-- The ratio identity is stated entirely in the original Gaussian
integrals at shifted and pure-kinetic precision. -/
theorem actual_same_vertex_reference_ratio {A b : ℝ} (hA : 0 < A)
    (hp : 0 < A + b) (n : ℕ) (hn : 1 ≤ n) :
    ((iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n
          (fun t => Real.log (actualPartition (A + b) b s t)) 0) 0) /
      gaussianDerivativeCoefficient (3 * n)) /
      ((iteratedDeriv (2 * n) (fun s => Real.log (actualPartition A 0 s 0)) 0) /
        gaussianDerivativeCoefficient (2 * n)) = capacity A b ^ n := by
  rw [actual_mixed_connected_derivative hp n hn,
    actual_pure_kinetic_connected_derivative hA n hn]
  simpa only [mixed_connected_derivative _ _ n hn,
    pure_kinetic_connected_derivative A n hn] using
    same_vertex_reference_ratio hA hp n hn

end GeneratedFoundations.Physical.SourceTTTensorConnectedResponse
