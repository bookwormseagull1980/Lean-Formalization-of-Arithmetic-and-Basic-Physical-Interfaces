module

public import GeneratedFoundations.Physical.SourceTTGaussianCoefficient
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Mass comparison in the retained TT source trace

The precision, kinetic insertion, species weights and Gaussian frequency
domain are those of `SourceTTGaussianCoefficient`. Only the common mass
insertion varies. The Gaussian envelope and its spectral projection stay
fixed, as in the logarithmic mass comparison used to define the reference
profile. Differentiation is performed under the actual frequency integral.

Three quantities have different roles: the kinetic response, its mass
derivative, and the weight of the comparison trace. The single-mode bound
transports to the second quantity with the third as its coefficient. It
does not identify that bound with the first quantity. No endpoint rule,
source update or admissibility predicate is introduced here.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace GeneratedFoundations.Physical.SourceTTCollectiveComparison

open SourceTensorResponseEndpoint SourceTTResponseNormalization

def envelope (a u : ℝ) : ℝ := Real.exp (-(u ^ 2 + a) / Real.pi)

def kineticProfile (a b z u : ℝ) : ℝ :=
  ttKernel (u ^ 2 + a) (Real.exp z * b) * envelope a u

def capacityProfile (a b z u : ℝ) : ℝ :=
  massWeightedResponse (massFraction (u ^ 2 + a) (Real.exp z * b)) * envelope a u

private theorem precision_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    0 < u ^ 2 + a + Real.exp z * b := by
  have hm := mul_pos (Real.exp_pos z) hb
  nlinarith [sq_nonneg u]

theorem kineticProfile_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z : ℝ) :
    Continuous (kineticProfile a b z) := by
  have hq : Continuous (fun u : ℝ => u ^ 2 + a) := by fun_prop
  have hp : Continuous (fun u : ℝ => u ^ 2 + a + Real.exp z * b) := by fun_prop
  have hw : Continuous (envelope a) := by unfold envelope; fun_prop
  exact ((hq.pow 2).div (hp.pow 2)
    (fun u => pow_ne_zero 2 (precision_pos ha hb z u).ne')).mul hw

theorem capacityProfile_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z : ℝ) :
    Continuous (capacityProfile a b z) := by
  have hp : Continuous (fun u : ℝ => u ^ 2 + a + Real.exp z * b) := by fun_prop
  have hy : Continuous (fun u : ℝ => Real.exp z * b / (u ^ 2 + a + Real.exp z * b)) :=
    continuous_const.div hp (fun u => (precision_pos ha hb z u).ne')
  have hw : Continuous (envelope a) := by unfold envelope; fun_prop
  exact (hy.mul ((continuous_const.sub hy).pow 2)).mul hw

theorem capacityProfile_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    0 ≤ capacityProfile a b z u ∧
      capacityProfile a b z u ≤ (4 / 27 : ℝ) * envelope a u := by
  have hq : 0 ≤ u ^ 2 + a := add_nonneg (sq_nonneg u) ha
  have hm := (mul_pos (Real.exp_pos z) hb).le
  obtain ⟨hy0, hy1⟩ := massFraction_mem_unitInterval hq hm (precision_pos ha hb z u)
  have hw : 0 ≤ envelope a u := (Real.exp_pos _).le
  exact ⟨mul_nonneg (mul_nonneg hy0 (sq_nonneg _)) hw,
    mul_le_mul_of_nonneg_right (massWeightedResponse_le hy0 hy1) hw⟩

theorem capacityProfile_le_kineticProfile {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    capacityProfile a b z u ≤ kineticProfile a b z u := by
  have hq : 0 ≤ u ^ 2 + a := add_nonneg (sq_nonneg u) ha
  have hm := (mul_pos (Real.exp_pos z) hb).le
  have hy := (massFraction_mem_unitInterval hq hm (precision_pos ha hb z u)).2
  unfold capacityProfile kineticProfile
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [ttKernel_eq_massFraction _ _ (precision_pos ha hb z u).ne']
  unfold massWeightedResponse
  exact (mul_le_mul_of_nonneg_right hy (sq_nonneg _)).trans_eq (one_mul _)

theorem kineticProfile_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    HasDerivAt (fun t => kineticProfile a b t u) (-2 * capacityProfile a b z u) z := by
  have hd := (logMassKernel_hasDerivAt (u ^ 2 + a) b z
    (precision_pos ha hb z u).ne').mul_const (envelope a u)
  simpa only [kineticProfile, capacityProfile, logMassKernel, mul_assoc] using hd

/-- Exact differentiation of the retained frequency response. The bound
is uniform in the mass parameter and retains the Gaussian envelope. -/
theorem frequency_response_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z v : ℝ) :
    HasDerivAt (fun t => ∫ u in (0 : ℝ)..v, kineticProfile a b t u)
      (-2 * ∫ u in (0 : ℝ)..v, capacityProfile a b z u) z := by
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t u => kineticProfile a b t u)
    (F' := fun t u => -2 * capacityProfile a b t u)
    (bound := fun u => (8 / 27 : ℝ) * envelope a u)
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ nhds z)
    (Filter.Eventually.of_forall fun t =>
      (kineticProfile_continuous ha hb t).aestronglyMeasurable)
    ((kineticProfile_continuous ha hb z).intervalIntegrable _ _)
    ((continuous_const.mul (capacityProfile_continuous ha hb z)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u _ t _ => by
      obtain ⟨h0, h1⟩ := capacityProfile_bounds ha hb t u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      norm_num
      linarith)
    (show IntervalIntegrable (fun u => (8 / 27 : ℝ) * envelope a u) volume 0 v from
      (by unfold envelope; fun_prop : Continuous (fun u => (8 / 27 : ℝ) * envelope a u)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun u _ t _ => kineticProfile_hasDerivAt ha hb t u)).2
  simpa only [intervalIntegral.integral_const_mul] using hd

abbrev Branch := Fin 8

def upper (i : Branch) : ℝ :=
  Real.sqrt (5 * Real.pi - (SourceTTGaussianCoefficient.branch i).1)

def kineticIntegral (z : ℝ) (i : Branch) : ℝ :=
  ∫ u in (0 : ℝ)..upper i,
    kineticProfile (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z u

def capacityIntegral (z : ℝ) (i : Branch) : ℝ :=
  ∫ u in (0 : ℝ)..upper i,
    capacityProfile (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z u

def weightIntegral (i : Branch) : ℝ :=
  ∫ u in (0 : ℝ)..upper i, envelope (SourceTTGaussianCoefficient.branch i).1 u

def massCoefficient (z : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 * kineticIntegral z i

def capacityCoefficient (z : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 * capacityIntegral z i

def weightCoefficient : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 * weightIntegral i

/-- At zero mass deformation this is exactly the existing integral, with
all colour, species and frequency weights unchanged. -/
theorem massCoefficient_zero : massCoefficient 0 = SourceTTGaussianCoefficient.coefficient := by
  simp only [massCoefficient, SourceTTGaussianCoefficient.coefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold kineticIntegral upper SourceTTGaussianCoefficient.branchIntegral
    kineticProfile SourceTTGaussianCoefficient.kernel ttKernel envelope
  simp only [Real.exp_zero, one_mul, div_pow]

theorem massCoefficient_pos (z : ℝ) : 0 < massCoefficient z := by
  apply mul_pos (by positivity : (0 : ℝ) < 1 / (32 * Real.pi ^ 3))
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
  have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
  apply mul_pos (SourceTTGaussianCoefficient.branch_bounds i).2.2.2
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((kineticProfile_continuous ha hb z).intervalIntegrable _ _)
    (fun u hu => ?_)
    (Real.sqrt_pos.2 (sub_pos.2 (SourceTTGaussianCoefficient.branch_bounds i).2.1))
  have hq : 0 < u ^ 2 + (SourceTTGaussianCoefficient.branch i).1 :=
    lt_of_lt_of_le (sq_pos_of_pos hu.1) (le_add_of_nonneg_right ha)
  exact mul_pos (div_pos (sq_pos_of_pos hq)
    (sq_pos_of_pos (precision_pos ha hb z u))) (Real.exp_pos _)

theorem capacityCoefficient_pos (z : ℝ) : 0 < capacityCoefficient z := by
  apply mul_pos (by positivity : (0 : ℝ) < 1 / (32 * Real.pi ^ 3))
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
  have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
  apply mul_pos (SourceTTGaussianCoefficient.branch_bounds i).2.2.2
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((capacityProfile_continuous ha hb z).intervalIntegrable _ _)
    (fun u hu => ?_)
    (Real.sqrt_pos.2 (sub_pos.2 (SourceTTGaussianCoefficient.branch_bounds i).2.1))
  have hq : 0 < u ^ 2 + (SourceTTGaussianCoefficient.branch i).1 :=
    lt_of_lt_of_le (sq_pos_of_pos hu.1) (le_add_of_nonneg_right ha)
  have hp := precision_pos ha hb z u
  have hy : 0 < massFraction (u ^ 2 + (SourceTTGaussianCoefficient.branch i).1)
      (Real.exp z * (SourceTTGaussianCoefficient.branch i).2.1) :=
    div_pos (mul_pos (Real.exp_pos z) hb) hp
  have hy1 : massFraction (u ^ 2 + (SourceTTGaussianCoefficient.branch i).1)
      (Real.exp z * (SourceTTGaussianCoefficient.branch i).2.1) < 1 := by
    rw [massFraction, div_lt_one hp]
    linarith
  exact mul_pos (mul_pos hy (sq_pos_of_pos (sub_pos.2 hy1))) (Real.exp_pos _)

theorem massCoefficient_hasDerivAt (z : ℝ) :
    HasDerivAt massCoefficient (-2 * capacityCoefficient z) z := by
  have hi (i : Branch) :=
    (frequency_response_hasDerivAt (SourceTTGaussianCoefficient.branch_bounds i).1
      (SourceTTGaussianCoefficient.branch_bounds i).2.2.1 z (upper i)).const_mul
        (SourceTTGaussianCoefficient.branch i).2.2
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i).const_mul
    (1 / (32 * Real.pi ^ 3))
  convert! hd using 1
  simp only [capacityCoefficient, capacityIntegral]
  rw [show -2 * ((1 / (32 * Real.pi ^ 3)) *
      ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 *
        ∫ u in (0 : ℝ)..upper i, capacityProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u) =
      (1 / (32 * Real.pi ^ 3)) * (-2 *
      ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 *
        ∫ u in (0 : ℝ)..upper i, capacityProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightCoefficient_pos : 0 < weightCoefficient := by
  apply mul_pos (by positivity : (0 : ℝ) < 1 / (32 * Real.pi ^ 3))
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  apply mul_pos (SourceTTGaussianCoefficient.branch_bounds i).2.2.2
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (show IntervalIntegrable (envelope (SourceTTGaussianCoefficient.branch i).1)
        volume 0 (upper i) from (by unfold envelope; fun_prop :
          Continuous (envelope (SourceTTGaussianCoefficient.branch i).1)).intervalIntegrable _ _)
    (fun _ _ => Real.exp_pos _)
  exact Real.sqrt_pos.2 (sub_pos.2 (SourceTTGaussianCoefficient.branch_bounds i).2.1)

/-- Transport of the modewise capacity bound to the actual trace. Its
coefficient is the complete Gaussian weight, not the number one. -/
theorem capacityCoefficient_bound (z : ℝ) :
    capacityCoefficient z ≤ (4 / 27 : ℝ) * weightCoefficient := by
  have hi (i : Branch) : capacityIntegral z i ≤ (4 / 27 : ℝ) * weightIntegral i := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
    rw [capacityIntegral, weightIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
      ((capacityProfile_continuous ha hb z).intervalIntegrable _ _)
      ((by unfold envelope; fun_prop : Continuous
        (fun u => (4 / 27 : ℝ) * envelope (SourceTTGaussianCoefficient.branch i).1 u)).intervalIntegrable _ _)
    exact fun u _ => (capacityProfile_bounds ha hb z u).2
  unfold capacityCoefficient weightCoefficient
  calc
    _ ≤ (1 / (32 * Real.pi ^ 3)) *
        ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 *
          ((4 / 27 : ℝ) * weightIntegral i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hi i)
          (SourceTTGaussianCoefficient.branch_bounds i).2.2.2.le) (by positivity)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem capacityCoefficient_le_massCoefficient (z : ℝ) :
    capacityCoefficient z ≤ massCoefficient z := by
  have hi (i : Branch) : capacityIntegral z i ≤ kineticIntegral z i := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
    exact intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
      ((capacityProfile_continuous ha hb z).intervalIntegrable _ _)
      ((kineticProfile_continuous ha hb z).intervalIntegrable _ _)
      (fun u _ => capacityProfile_le_kineticProfile ha hb z u)
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hi i)
      (SourceTTGaussianCoefficient.branch_bounds i).2.2.2.le) (by positivity)

/-- The mass fraction actually read by the collective logarithmic response.
It is derived from the original trace, rather than a free single-mode split. -/
def effectiveMassFraction (z : ℝ) : ℝ := capacityCoefficient z / massCoefficient z

theorem effectiveMassFraction_bounds (z : ℝ) :
    0 < effectiveMassFraction z ∧ effectiveMassFraction z ≤ 1 := by
  exact ⟨div_pos (capacityCoefficient_pos z) (massCoefficient_pos z),
    (div_le_one (massCoefficient_pos z)).2 (capacityCoefficient_le_massCoefficient z)⟩

def response (c z : ℝ) : ℝ := massCoefficient z / c

def massResponse (c z : ℝ) : ℝ := capacityCoefficient z / c

def traceWeight (c : ℝ) : ℝ := weightCoefficient / c

theorem response_hasDerivAt (c z : ℝ) :
    HasDerivAt (response c) (-2 * massResponse c z) z := by
  convert! (massCoefficient_hasDerivAt z).div_const c using 1
  simp only [massResponse, mul_div_assoc]

/-- Averaging by the same source trace removes its homogeneous radius
factor. It changes neither species weights nor the reference mass path. -/
theorem normalized_response {c : ℝ} (hc : c ≠ 0) (z : ℝ) :
    response c z / traceWeight c = massCoefficient z / weightCoefficient := by
  unfold response traceWeight
  field_simp [hc, weightCoefficient_pos.ne']

theorem normalized_massResponse {c : ℝ} (hc : c ≠ 0) (z : ℝ) :
    massResponse c z / traceWeight c = capacityCoefficient z / weightCoefficient := by
  unfold massResponse traceWeight
  field_simp [hc, weightCoefficient_pos.ne']

theorem normalized_massResponse_bound {c : ℝ} (hc : c ≠ 0) (z : ℝ) :
    massResponse c z / traceWeight c ≤ (4 / 27 : ℝ) := by
  rw [normalized_massResponse hc, div_le_iff₀ weightCoefficient_pos]
  exact capacityCoefficient_bound z

/-- The existing endpoint rule can be transported along this actual mass
comparison. This definition retains that rule; it does not derive it. -/
def matchedRadius (z : ℝ) : ℝ := endpointRoot (massCoefficient z)

theorem matchedRadius_zero : matchedRadius 0 = SourceTTGaussianCoefficient.radius := by
  rw [matchedRadius, massCoefficient_zero]
  rfl

theorem matchedRadius_response (z : ℝ) : response (matchedRadius z) z = 4 / 27 := by
  exact sub_eq_zero.mp (endpointResidual_root (massCoefficient_pos z))

theorem matchedRadius_hasDerivAt (z : ℝ) :
    HasDerivAt matchedRadius (-27 * capacityCoefficient z / 2) z := by
  convert! ((massCoefficient_hasDerivAt z).const_mul 27).div_const 4 using 1
  ring

theorem matchedRadius_deriv_neg (z : ℝ) : deriv matchedRadius z < 0 := by
  rw [(matchedRadius_hasDerivAt z).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (capacityCoefficient_pos z))
    (by norm_num)

theorem matchedRadius_log_hasDerivAt (z : ℝ) :
    HasDerivAt (fun t => Real.log (matchedRadius t)) (-2 * effectiveMassFraction z) z := by
  have hp : 0 < matchedRadius z := endpointRoot_pos (massCoefficient_pos z)
  convert! (matchedRadius_hasDerivAt z).log hp.ne' using 1
  unfold matchedRadius endpointRoot effectiveMassFraction
  field_simp [(massCoefficient_pos z).ne']
  ring

end GeneratedFoundations.Physical.SourceTTCollectiveComparison
