module

public import GeneratedFoundations.Arithmetic.HistoryDetailCasimir
public import GeneratedFoundations.Arithmetic.HistoryRightChargeQuotient
public import GeneratedFoundations.Arithmetic.HistoryChargedTransport

/-!
# The joint charge response with its internally computed detail Casimir

The detail operator is the complete trace-dual generator sum on the actual
phase-residual space. It acts at every original source coordinate. The other
term is the adjoint square of the already normalized integer charge. Thus
neither a colour coefficient nor a neutral line is supplied as new data.

The neutral-kernel comparison is proved for `n >= 2`. The smaller phase
fibres remain covered by the operator and positivity definitions, but their
extra zero-charge sectors are not silently identified with this kernel.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryChargedCasimirResponse

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)
open HistoryJointQuadraticResponse (RightSpace rightInclusion rightCharge)

def detailResponse (n : ℕ) : Module.End ℂ (Space n) :=
  blocks n (fun _ => HistoryDetailCasimir.response n)

def chargeSquare (n : ℕ) : Module.End ℂ (Space n) :=
  (HistoryChargeContent.normalizedResponse n).adjoint *
    HistoryChargeContent.normalizedResponse n

def response (n : ℕ) : Module.End ℂ (Space n) := detailResponse n + chargeSquare n

theorem detailResponse_symmetric (n : ℕ) (x y : Space n) :
    inner ℂ (detailResponse n x) y = inner ℂ x (detailResponse n y) := by
  change (∑ s : Spin, inner ℂ (detailResponse n x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (detailResponse n y s)
  apply Finset.sum_congr rfl
  intro s _
  simpa only [detailResponse, blocks_apply] using
    HistoryDetailCasimir.response_symmetric n (x s) (y s)

theorem detailResponse_quadratic (n : ℕ) (x : Space n) :
    (inner ℂ x (detailResponse n x)).re =
      HistoryDetailCasimir.coefficient n * ∑ s : Spin, ‖residual n (x s)‖ ^ 2 := by
  change (∑ s : Spin, inner ℂ (x s) (detailResponse n x s)).re = _
  rw [Complex.re_sum]
  simp only [detailResponse, blocks_apply, HistoryDetailCasimir.quadratic_eq]
  exact (Finset.mul_sum _ _ _).symm

theorem detailResponse_positive (n : ℕ) : (detailResponse n).IsPositive := by
  refine ⟨detailResponse_symmetric n, fun x => ?_⟩
  change 0 ≤ (inner ℂ (detailResponse n x) x).re
  rw [congrArg Complex.re (detailResponse_symmetric n x x), detailResponse_quadratic]
  exact mul_nonneg (HistoryDetailCasimir.coefficient_nonneg n)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem chargeSquare_quadratic (n : ℕ) (x : Space n) :
    (inner ℂ x (chargeSquare n x)).re =
      ‖HistoryChargeContent.normalizedResponse n x‖ ^ 2 := by
  change (inner ℂ x ((HistoryChargeContent.normalizedResponse n).adjoint
    (HistoryChargeContent.normalizedResponse n x))).re = _
  rw [LinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (HistoryChargeContent.normalizedResponse n x)

theorem chargeSquare_positive (n : ℕ) : (chargeSquare n).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self _

theorem response_positive (n : ℕ) : (response n).IsPositive :=
  (detailResponse_positive n).add (chargeSquare_positive n)

theorem response_adjoint (n : ℕ) : (response n).adjoint = response n :=
  (response_positive n).adjoint_eq

theorem response_quadratic (n : ℕ) (x : Space n) :
    (inner ℂ x (response n x)).re =
      HistoryDetailCasimir.coefficient n * ∑ s : Spin, ‖residual n (x s)‖ ^ 2 +
        ‖HistoryChargeContent.normalizedResponse n x‖ ^ 2 := by
  simp only [response, LinearMap.add_apply, inner_add_right, Complex.add_re,
    detailResponse_quadratic, chargeSquare_quadratic]

theorem normalized_zero_iff {n : ℕ} (hn : 0 < n) (x : Space n) :
    HistoryChargeContent.normalizedResponse n x = 0 ↔ generatedResponse n x = 0 := by
  have hc : (2 * n : ℂ)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast hn.ne'))
  change (2 * n : ℂ)⁻¹ • generatedResponse n x = 0 ↔ _
  simp only [smul_eq_zero, hc, false_or]

theorem neutral_detail_zero {n : ℕ} (hn : 2 ≤ n) {x : Space n}
    (hx : x ∈ neutral n) (s : Spin) : residual n (x s) = 0 := by
  have hw : generatedWeight n (true, s) ≠ 0 := by
    intro h
    have he := (generated_zero_iff hn (true, s)).mp h
    simp at he
  have hc : (generatedWeight n (true, s) : ℂ) ≠ 0 := by exact_mod_cast hw
  exact (smul_eq_zero.mp (((neutral_iff n x).mp hx s).2)).resolve_left hc

theorem response_zero_iff {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    response n x = 0 ↔ x ∈ neutral n := by
  have hn' : 0 < n := by omega
  constructor
  · intro hx
    have he : HistoryDetailCasimir.coefficient n *
        ∑ s : Spin, ‖residual n (x s)‖ ^ 2 +
          ‖HistoryChargeContent.normalizedResponse n x‖ ^ 2 = 0 := by
      rw [← response_quadratic, hx, inner_zero_right]
      rfl
    have hd := mul_nonneg (HistoryDetailCasimir.coefficient_nonneg n)
      (Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) => sq_nonneg ‖residual n (x s)‖))
    have hc : ‖HistoryChargeContent.normalizedResponse n x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖HistoryChargeContent.normalizedResponse n x‖]
    exact (normalized_zero_iff hn' x).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hc))
  · intro hx
    have hd : detailResponse n x = 0 := by
      apply PiLp.ext
      intro s
      simp only [detailResponse, blocks_apply, PiLp.zero_apply,
        HistoryDetailCasimir.response_eq, LinearMap.smul_apply,
        neutral_detail_zero hn hx s, smul_zero]
    have hc := (normalized_zero_iff hn' x).mpr hx
    simp [response, hd, chargeSquare, Module.End.mul_apply, hc]

theorem response_kernel {n : ℕ} (hn : 2 ≤ n) :
    LinearMap.ker (response n) = neutral n := by
  ext x
  exact response_zero_iff hn x

def rightDetailResponse (n : ℕ) : Module.End ℂ (RightSpace n) where
  toFun x := WithLp.toLp 2 fun i => HistoryDetailCasimir.response n (x i)
  map_add' x y := by apply PiLp.ext; intro i; exact map_add _ _ _
  map_smul' c x := by
    apply PiLp.ext
    intro i
    exact map_smul (HistoryDetailCasimir.response n) c (x i)

def rightNormalizedCharge (n : ℕ) : Module.End ℂ (RightSpace n) :=
  (2 * n : ℂ)⁻¹ • rightCharge n

def rightResponse (n : ℕ) : Module.End ℂ (RightSpace n) :=
  rightDetailResponse n + rightNormalizedCharge n * rightNormalizedCharge n

theorem detailResponse_right (n : ℕ) (x : RightSpace n) :
    detailResponse n (rightInclusion n x) = rightInclusion n (rightDetailResponse n x) := by
  apply PiLp.ext
  intro s
  cases s <;> simp [detailResponse, blocks_apply, rightDetailResponse]

theorem normalized_right (n : ℕ) (x : RightSpace n) :
    HistoryChargeContent.normalizedResponse n (rightInclusion n x) =
      rightInclusion n (rightNormalizedCharge n x) := by
  simp [HistoryChargeContent.normalizedResponse, rightNormalizedCharge,
    HistoryJointQuadraticResponse.generatedResponse_right, map_smul]

theorem response_right (n : ℕ) (x : RightSpace n) :
    response n (rightInclusion n x) = rightInclusion n (rightResponse n x) := by
  simp [response, rightResponse, chargeSquare,
    HistoryJointQuadraticResponse.normalizedResponse_adjoint,
    detailResponse_right, Module.End.mul_apply, normalized_right, map_add]

theorem rightResponse_symmetric (n : ℕ) (x y : RightSpace n) :
    inner ℂ (rightResponse n x) y = inner ℂ x (rightResponse n y) := by
  rw [← HistoryJointQuadraticResponse.rightInclusion_inner n,
    ← HistoryJointQuadraticResponse.rightInclusion_inner n,
    ← response_right, ← response_right]
  exact (response_positive n).isSymmetric _ _

theorem rightResponse_positive (n : ℕ) : (rightResponse n).IsPositive := by
  refine ⟨rightResponse_symmetric n, fun x => ?_⟩
  rw [← HistoryJointQuadraticResponse.rightInclusion_inner n, ← response_right]
  exact (response_positive n).re_inner_nonneg_left _

theorem rightResponse_adjoint (n : ℕ) : (rightResponse n).adjoint = rightResponse n :=
  (rightResponse_positive n).adjoint_eq

theorem rightResponse_kernel {n : ℕ} (hn : 2 ≤ n) :
    LinearMap.ker (rightResponse n) = HistoryRightChargeQuotient.RightNeutral n := by
  ext x
  change rightResponse n x = 0 ↔ x ∈ LinearMap.ker (rightCharge n)
  rw [HistoryJointQuadraticResponse.rightNeutral_iff]
  rw [← response_zero_iff hn, response_right]
  exact (map_eq_zero_iff _ (HistoryJointQuadraticResponse.rightInclusion_injective n)).symm

theorem rightQuotient_finrank {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (RightSpace n ⧸ LinearMap.ker (rightResponse n)) =
      (2 * n + 1) * HistoryChargeContent.historyCount n := by
  rw [rightResponse_kernel hn]
  exact HistoryRightChargeQuotient.rightChargedQuotient_finrank hn

theorem detailResponse_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (detailResponse n) =
      4 * (HistoryDetailCasimir.coefficient n : ℂ) *
        (n * Fintype.card (CompleteHistory.History (n + 1))) := by
  rw [detailResponse, blocks_trace]
  simp only [HistoryDetailCasimir.response_eq, map_smul,
    HistoryPhaseProjection.residual_trace, smul_eq_mul,
    Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem response_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (response n) =
      4 * (HistoryDetailCasimir.coefficient n : ℂ) *
        (n * Fintype.card (CompleteHistory.History (n + 1))) +
          (HistoryChargeContent.chargeSqSum n : ℂ) := by
  rw [response, map_add, detailResponse_trace, chargeSquare,
    HistoryJointQuadraticResponse.normalizedResponse_adjoint,
    HistoryChargeContent.normalizedResponse_sq_trace]

theorem detail_phase_commutes (n : ℕ) (q : ZMod (n + 1)) :
    HistoryChargedTransport.phaseTransport n q * detailResponse n =
      detailResponse n * HistoryChargedTransport.phaseTransport n q := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [Module.End.mul_apply, HistoryChargedTransport.phaseTransport_apply,
    detailResponse, blocks_apply, HistoryDetailCasimir.response_eq, LinearMap.smul_apply]
  rw [map_smul]
  congr 1
  simp [HistoryPhaseProjection.residual, HistoryPhaseProjection.translation_projection,
    HistoryPhaseProjection.projection_translation]

theorem charge_phase_commutes (n : ℕ) (q : ZMod (n + 1)) :
    HistoryChargedTransport.phaseTransport n q * HistoryChargeContent.normalizedResponse n =
      HistoryChargeContent.normalizedResponse n * HistoryChargedTransport.phaseTransport n q := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [Module.End.mul_apply, HistoryChargeContent.normalizedResponse,
    generatedResponse, HistoryJointCharge.response, blocks_apply,
    component, HistoryRelativePhase.block_apply, HistoryPhaseProjection.residual,
    HistoryPhaseProjection.translation_projection, HistoryPhaseProjection.projection_translation]

theorem response_phase_commutes (n : ℕ) (q : ZMod (n + 1)) :
    HistoryChargedTransport.phaseTransport n q * response n =
      response n * HistoryChargedTransport.phaseTransport n q := by
  rw [response, mul_add, add_mul, detail_phase_commutes, chargeSquare,
    HistoryJointQuadraticResponse.normalizedResponse_adjoint]
  have h := charge_phase_commutes n q
  congr 1
  rw [← mul_assoc, h, mul_assoc, h, mul_assoc]

theorem response_retained {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    response n (HistoryChargedReconstruction.quotientRetained n
      ((neutral n).mkQ x) : Space n) = response n x := by
  rw [HistoryChargedReconstruction.quotientRetained_apply]
  change response n (x - HistoryJointChargeQuotient.neutralProjection n x) = _
  have hm : HistoryJointChargeQuotient.neutralProjection n x ∈ neutral n :=
    (HistoryJointChargeQuotient.neutralProjection_fixed_iff n
      (HistoryJointChargeQuotient.neutralProjection n x)).mp
      (LinearMap.congr_fun (HistoryJointChargeQuotient.neutralProjection_idempotent n) x)
  rw [map_sub, (response_zero_iff hn _).mpr hm, sub_zero]

structure Conclusions : Prop where
  derived_coefficient : ∀ n, HistoryDetailCasimir.coefficient n =
    Operations.FiniteDefiningResponse.coefficient (HistoryDetailCasimir.Detail n)
  full_positive : ∀ n, (response n).IsPositive
  full_adjoint : ∀ n, (response n).adjoint = response n
  full_quadratic : ∀ n x, (inner ℂ x (response n x)).re =
    HistoryDetailCasimir.coefficient n * ∑ s : Spin, ‖residual n (x s)‖ ^ 2 +
      ‖HistoryChargeContent.normalizedResponse n x‖ ^ 2
  actual_kernel : ∀ n, 2 ≤ n → LinearMap.ker (response n) = neutral n
  right_restriction : ∀ n x,
    response n (rightInclusion n x) = rightInclusion n (rightResponse n x)
  right_positive : ∀ n, (rightResponse n).IsPositive
  actual_right_kernel : ∀ n, 2 ≤ n →
    LinearMap.ker (rightResponse n) = HistoryRightChargeQuotient.RightNeutral n
  right_quotient_rank : ∀ n, 2 ≤ n →
    Module.finrank ℂ (RightSpace n ⧸ LinearMap.ker (rightResponse n)) =
      (2 * n + 1) * HistoryChargeContent.historyCount n
  generated_phase_covariance : ∀ n q,
    HistoryChargedTransport.phaseTransport n q * response n =
      response n * HistoryChargedTransport.phaseTransport n q
  retained_response : ∀ n, 2 ≤ n → ∀ x,
    response n (HistoryChargedReconstruction.quotientRetained n
      ((neutral n).mkQ x) : Space n) = response n x

theorem generated : Conclusions where
  derived_coefficient := fun _ => rfl
  full_positive := response_positive
  full_adjoint := response_adjoint
  full_quadratic := response_quadratic
  actual_kernel := fun _ => response_kernel
  right_restriction := response_right
  right_positive := rightResponse_positive
  actual_right_kernel := fun _ => rightResponse_kernel
  right_quotient_rank := fun _ => rightQuotient_finrank
  generated_phase_covariance := response_phase_commutes
  retained_response := fun _ => response_retained

end GeneratedFoundations.Arithmetic.HistoryChargedCasimirResponse
