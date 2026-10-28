module

public import GeneratedFoundations.Physical.SourceTTGaussianCoefficient

/-!
# Endpoint balance in the original quadratic source

The effective action below is a direct comparison cost minus the logarithm
of the actual Gaussian partition. Differentiating it retains the complete
precision path, including its direct second vertex. A zero of this Hessian
equates the score variance to the direct comparison response plus the mean
second vertex.

For the kinetic insertion already used in the TT coefficient, the source
part of the Hessian is minus one half of the two-leg kernel. Consequently
the existing endpoint equation follows from a zero Hessian precisely when
the remaining direct response has the required value. This value is an
explicit hypothesis in that implication; it is not inferred from the
modewise maximum. All threshold-family statements below keep the original
spectral coefficient and source law fixed.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace GeneratedFoundations.Physical.SourceTTEndpointBalance

open Operations SourceTensorResponseEndpoint SourceTTResponseNormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The action and its complete second variation -/

/-- The comparison is evaluated in the original reference Gaussian, before
performing the source integral. `C` is the actual direct comparison cost. -/
def effectiveAction (p : ℝ → ι → ℝ) (r : ℝ) (C : ℝ → ℝ) (z : ℝ) : ℝ :=
  C z - Real.log (FinitePrecisionPath.partition p r z)

omit [DecidableEq ι] in
private theorem precision_eventually_pos (p v : ℝ → ι → ℝ) (z : ℝ)
    (hp : ∀ i, 0 < p z i)
    (hv : ∀ i, HasDerivAt (fun t => p t i) (v z i) z) :
    ∀ᶠ t in nhds z, ∀ i, 0 < p t i := by
  exact Filter.eventually_all.2 fun i =>
    (hv i).continuousAt.eventually (eventually_gt_nhds (hp i))

/-- First variation of the actual logarithmic integral. The force is the
mean of the derivative of the same quadratic action. -/
theorem effectiveAction_hasDerivAt
    (p v : ℝ → ι → ℝ) (r z : ℝ) (C : ℝ → ℝ) (b : ℝ)
    (hr : ∀ i, 0 < p r i) (hp : ∀ i, 0 < p z i)
    (hv : ∀ i, HasDerivAt (fun t => p t i) (v z i) z)
    (hC : HasDerivAt C b z) :
    HasDerivAt (effectiveAction p r C)
      (b + FinitePrecisionPath.force p v z) z := by
  have hd := hC.sub (FinitePrecisionPath.logPartition_hasDerivAt (r := r) hp hv)
  simp only [sub_neg_eq_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [precision_eventually_pos p v z hp hv] with t ht
  simp only [effectiveAction, FinitePrecisionPath.log_partition hr ht, Pi.sub_apply]

/-- Exact Hessian of the first variation. The first summand is the direct
comparison response; the second is the mean of the source's second vertex. -/
theorem effectiveGradient_hasDerivAt
    (p v a : ℝ → ι → ℝ) (B : ℝ → ℝ) (z Z : ℝ)
    (hp : ∀ i, 0 < p z i)
    (hv : ∀ i, HasDerivAt (fun t => p t i) (v z i) z)
    (ha : ∀ i, HasDerivAt (fun t => v t i) (a z i) z)
    (hB : HasDerivAt B Z z) :
    HasDerivAt (fun t => B t + FinitePrecisionPath.force p v t)
      (Z + (∫ x, FinitePrecisionGaussian.score (a z) x
        ∂FinitePrecisionGaussian.law (p z)) -
        Var[FinitePrecisionGaussian.score (v z);
          FinitePrecisionGaussian.law (p z)]) z := by
  have hd := hB.add (FinitePrecisionPath.force_hasDerivAt hp hv ha)
  rwa [FinitePrecisionPath.curvature_eq_mean_sub_variance hp, ← add_sub_assoc] at hd

/-- Vanishing complete Hessian is a balance with both direct terms. -/
theorem full_criticality_iff (p v a : ℝ → ι → ℝ) (z Z : ℝ)
    (hp : ∀ i, 0 < p z i) :
    Z + FinitePrecisionPath.curvature p v a z = 0 ↔
      Var[FinitePrecisionGaussian.score (v z);
        FinitePrecisionGaussian.law (p z)] =
        Z + ∫ x, FinitePrecisionGaussian.score (a z) x
          ∂FinitePrecisionGaussian.law (p z) := by
  rw [FinitePrecisionPath.curvature_eq_mean_sub_variance hp]
  constructor <;> intro h <;> linarith

/-! ## The original kinetic insertion -/

def kineticEffectiveAction (q2 m2 : ι → ℝ) (Z z : ℝ) : ℝ :=
  Z * z ^ 2 / 2 - kineticLogPartition q2 m2 z

theorem kineticEffectiveAction_hasDerivAt (q2 m2 : ι → ℝ) (Z z : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i)
    (hz : ∀ i, 0 < q2 i + m2 i + z * q2 i) :
    HasDerivAt (kineticEffectiveAction q2 m2 Z)
      (Z * z - deriv (kineticLogPartition q2 m2) z) z := by
  have hlog := kineticLogPartition_hasDerivAt q2 m2 z hp hz
  have hd := ((((hasDerivAt_id z).pow 2).const_mul Z).div_const 2).sub hlog
  convert! hd using 1
  rw [hlog.deriv]
  simp only [id_eq]
  ring

/-- The factor one half is fixed by the original real Gaussian integral. -/
theorem kineticEffectiveGradient_hasDerivAt (q2 m2 : ι → ℝ) (Z : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    HasDerivAt
      (fun z => Z * z - deriv (kineticLogPartition q2 m2) z)
      (Z - gaussianKineticResponse q2 m2 / 2) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).const_mul Z).sub
    (kineticLogPartition_second_response q2 m2 hp)
  convert! hd using 1; simp

theorem kinetic_criticality_iff (q2 m2 : ι → ℝ) (Z : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    Z - gaussianKineticResponse q2 m2 / 2 = 0 ↔
      (∑ i, ttKernel (q2 i) (m2 i)) = 2 * Z := by
  rw [gaussianKineticResponse_eq q2 m2 hp]
  constructor <;> intro h <;> linarith

/-! ## What would select the matching value -/

/-- Algebraic form obtained after identifying the fixed spectral response
with the integrated source variance and retaining its direct response. -/
def reducedHessian (A κ Z c : ℝ) : ℝ := Z - κ * (A / c) / 2

theorem reduced_criticality_iff {A κ Z c : ℝ} (hκ : 0 < κ) :
    reducedHessian A κ Z c = 0 ↔ A / c = 2 * Z / κ := by
  unfold reducedHessian
  field_simp [hκ.ne']
  constructor <;> intro h <;> nlinarith

/-- At a true critical point, matching to the modewise maximum is equivalent
to a specific value of the direct response in the same normalization. -/
theorem critical_endpoint_iff_direct_response {A κ Z c : ℝ}
    (hκ : 0 < κ) (hcrit : reducedHessian A κ Z c = 0) :
    A / c = (4 / 27 : ℝ) ↔ Z = 2 * κ / 27 := by
  have hb := (reduced_criticality_iff hκ).mp hcrit
  constructor
  · intro hm
    rw [hm] at hb
    have he := (eq_div_iff hκ.ne').mp hb
    linarith
  · intro hZ
    rw [hZ] at hb
    have he := (eq_div_iff hκ.ne').mp hb
    nlinarith

/-- This implication explicitly records the independent identity still
required of the generated direct response. -/
theorem endpoint_of_source_balance {A κ Z c : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hc : 0 < c)
    (hcrit : reducedHessian A κ Z c = 0) (hZ : Z = 2 * κ / 27) :
    c = endpointRoot A := by
  have hm := (critical_endpoint_iff_direct_response hκ hcrit).2 hZ
  exact (endpointResidual_eq_zero_iff hA hc).1 (sub_eq_zero.mpr hm)

/-- With the same source coefficient, a different positive direct response
has its own unique critical radius. -/
theorem reduced_critical_radius {A κ Z c : ℝ}
    (hκ : 0 < κ) (hZ : 0 < Z) (hc : 0 < c) :
    reducedHessian A κ Z c = 0 ↔ c = κ * A / (2 * Z) := by
  rw [reduced_criticality_iff hκ]
  constructor
  · intro h
    have he := (div_eq_div_iff hc.ne' hκ.ne').1 h
    apply (eq_div_iff (by positivity : 2 * Z ≠ 0)).2
    nlinarith
  · intro h
    apply (div_eq_div_iff hc.ne' hκ.ne').2
    have he := (eq_div_iff (by positivity : 2 * Z ≠ 0)).1 h
    nlinarith

/-! ## The scale law alone allows every positive matching level -/

theorem unique_crossing_at_any_level {A θ : ℝ} (hA : 0 < A) (hθ : 0 < θ) :
    ∃! c : ℝ, 0 < c ∧ A / c = θ := by
  refine ⟨A / θ, ⟨div_pos hA hθ, ?_⟩, ?_⟩
  · field_simp
  · intro c hc
    exact (eq_div_iff hθ.ne').2 (by
      have he := (div_eq_iff hc.1.ne').1 hc.2
      linarith)

/-- Both levels use the very same positive coefficient; neither changes a
spectral weight, precision, source law, or source-response identity. -/
theorem distinct_matching_levels {A θ η : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hη : 0 < η) (hne : θ ≠ η) :
    A / θ ≠ A / η := by
  intro he
  have hcross := (div_eq_div_iff hθ.ne' hη.ne').1 he
  apply hne
  nlinarith

/-- On the compact ladder's common homothetic path, the volume factor in
the vertex cancels the inverse factor in the sourced response. Its unit
feedback condition alone therefore supplies no equation for the radius. -/
theorem feedback_scale_cancellation (J D c : ℝ) (hD : D ≠ 0) (hc : c ≠ 0) :
    (c ^ 4 / D) * (J / c ^ 4) = J / D := by
  field_simp [hD, hc]

theorem fixed_source_all_positive_levels (θ : ℝ) (hθ : 0 < θ) :
    ∃! c : ℝ, 0 < c ∧ SourceTTGaussianCoefficient.response c = θ :=
  unique_crossing_at_any_level SourceTTGaussianCoefficient.coefficient_pos hθ

/-! ## Summing modes does not preserve equality in the single-mode bound -/

omit [DecidableEq ι] in
theorem weighted_response_defect (w y : ι → ℝ) :
    (4 / 27 : ℝ) * ∑ i, w i - ∑ i, w i * massWeightedResponse (y i) =
      ∑ i, w i * ((y i - 1 / 3) ^ 2 * (4 / 3 - y i)) := by
  simp_rw [← response_factorization]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- In the same Gaussian law a mode at the maximum of its logarithmic mass
response has kinetic response 4/9, rather than 4/27. -/
theorem mode_at_profile_maximum :
    massWeightedResponse (massFraction 2 1) = (4 / 27 : ℝ) ∧
      gaussianModeResponse 2 1 = (4 / 9 : ℝ) := by
  rw [gaussianModeResponse_eq 2 1 (by norm_num)]
  norm_num [massWeightedResponse, massFraction, ttKernel]

end GeneratedFoundations.Physical.SourceTTEndpointBalance
