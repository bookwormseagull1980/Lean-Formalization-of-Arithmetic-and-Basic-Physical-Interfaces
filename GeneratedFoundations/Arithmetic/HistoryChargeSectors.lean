module

public import GeneratedFoundations.Arithmetic.HistoryChargeRealization

/-!
# Complete charge sectors on the original arithmetic carrier

The two phase projections and the four original source coordinates give
eight mutually complementary subspaces. Each subspace retains every
history coefficient. The charge, its normalized square and the complete
detail response act there with the weights computed from their actual
operators. In particular a sector weight is not an independently assigned
label. The sum of these projections is the identity on the full carrier.

The invariant upper sector has zero canonical charge for every root. At
the smaller roots other zero-charge sectors may occur, as recorded in the
existing kernel classification; they are retained by this decomposition.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryChargeSectors

open HistoryJointCharge HistoryJointChargeLattice

def phaseProjection (n : ℕ) (c : Bool) : Module.End ℂ (Fibre n) :=
  if c then HistoryPhaseProjection.residual n else HistoryPhaseProjection.projection n

theorem phaseProjection_mul (n : ℕ) (c d : Bool) :
    phaseProjection n c * phaseProjection n d =
      if c = d then phaseProjection n c else 0 := by
  cases c <;> cases d <;>
    simp [phaseProjection, HistoryPhaseProjection.projection_idempotent,
      HistoryPhaseProjection.residual_idempotent,
      HistoryPhaseProjection.projection_residual,
      HistoryPhaseProjection.residual_projection]

theorem phaseProjection_sum (n : ℕ) :
    phaseProjection n false + phaseProjection n true = 1 := by
  simp [phaseProjection, HistoryPhaseProjection.residual]

def sectorSection (n : ℕ) (p : Sector) : Fibre n →ₗ[ℂ] Space n :=
  (inclusion n p.2).comp (phaseProjection n p.1)

def sectorProjection (n : ℕ) (p : Sector) : Module.End ℂ (Space n) :=
  (sectorSection n p).comp (sectionMap n p.2)

theorem sectorSection_apply (n : ℕ) (p : Sector) (x : Fibre n) (s : Spin) :
    sectorSection n p x s = if s = p.2 then phaseProjection n p.1 x else 0 := by
  classical
  by_cases hs : s = p.2 <;> simp [sectorSection, inclusion, hs]

theorem sectorProjection_apply (n : ℕ) (p : Sector) (x : Space n) (s : Spin) :
    sectorProjection n p x s =
      if s = p.2 then phaseProjection n p.1 (x p.2) else 0 :=
  sectorSection_apply n p (x p.2) s

theorem sectorProjection_sum (n : ℕ) : ∑ p : Sector, sectorProjection n p = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  classical
  change WithLp.ofLp (∑ p : Sector, sectorProjection n p x) s = x s
  rw [WithLp.ofLp_sum]
  change (∑ p : Sector, sectorProjection n p x s) = x s
  simp only [Fintype.sum_prod_type, sectorProjection_apply]
  have hs (c : Bool) : (∑ t : Spin,
      if s = t then phaseProjection n c (x t) else 0) = phaseProjection n c (x s) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_bool, hs, hs]
  have h := LinearMap.congr_fun (phaseProjection_sum n) (x s)
  simpa only [LinearMap.add_apply, Module.End.one_apply, add_comm] using h

theorem sectorProjection_mul (n : ℕ) (p q : Sector) :
    sectorProjection n p * sectorProjection n q =
      if p = q then sectorProjection n p else 0 := by
  classical
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  rcases p with ⟨c, i⟩
  rcases q with ⟨d, j⟩
  by_cases hij : i = j
  · subst j
    by_cases hsi : s = i
    · subst s
      simp only [Module.End.mul_apply, sectorProjection_apply, ite_true]
      have h := LinearMap.congr_fun (phaseProjection_mul n c d) (x i)
      cases c <;> cases d <;> simpa [sectorProjection_apply] using h
    · cases c <;> cases d <;> simp [Module.End.mul_apply, sectorProjection_apply, hsi]
  · simp [Module.End.mul_apply, sectorProjection_apply, hij, Prod.mk.injEq]

theorem sectorProjection_idempotent (n : ℕ) (p : Sector) :
    IsIdempotentElem (sectorProjection n p) := by
  rw [IsIdempotentElem]
  simpa using sectorProjection_mul n p p

theorem sectorProjection_trace (n : ℕ) (p : Sector) :
    LinearMap.trace ℂ (Space n) (sectorProjection n p) =
      if p.1 then (n * HistoryChargeContent.historyCount n : ℂ)
      else (HistoryChargeContent.historyCount n : ℂ) := by
  change LinearMap.trace ℂ (Space n)
    ((inclusion n p.2).comp ((phaseProjection n p.1).comp (sectionMap n p.2))) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, section_inclusion]
  change LinearMap.trace ℂ (Fibre n) (phaseProjection n p.1) = _
  cases p.1 <;> simp [phaseProjection, HistoryPhaseProjection.projection_trace,
    HistoryPhaseProjection.residual_trace, HistoryChargeContent.historyCount, mul_comm]

theorem sectorProjection_finrank (n : ℕ) (p : Sector) :
    Module.finrank ℂ (LinearMap.range (sectorProjection n p)) =
      if p.1 then n * HistoryChargeContent.historyCount n
      else HistoryChargeContent.historyCount n := by
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (sectorProjection_idempotent n p)).trace
  rw [sectorProjection_trace] at h
  by_cases hc : p.1 = true
  · simp only [hc, ite_true] at h ⊢
    exact_mod_cast h.symm
  · simp only [hc] at h ⊢
    exact_mod_cast h.symm

theorem sectorProjection_ne_zero {n : ℕ} (hn : 0 < n) (p : Sector) :
    sectorProjection n p ≠ 0 := by
  intro hz
  have hr := sectorProjection_finrank n p
  rw [hz, LinearMap.range_zero, finrank_bot] at hr
  have hH := HistoryChargeContent.historyCount_pos n
  by_cases hc : p.1 = true
  · simp only [hc, ite_true] at hr
    exact (Nat.mul_pos hn hH).ne' hr.symm
  · simp only [hc] at hr
    exact hH.ne' hr.symm

/-- Primitivity tested on occupied sectors agrees with the full integer
character test, because every sector has positive actual rank when n > 0. -/
theorem primitive_on_actual_sectors_iff {n : ℕ} (hn : 0 < n) (w : Sector → ℤ) :
    (∀ d : ℤ, (∀ p, sectorProjection n p ≠ 0 → d ∣ w p) → IsUnit d) ↔
      HistoryJointChargeClassification.PrimitiveWeights w := by
  constructor
  · intro hp d hd
    exact hp d (fun p _ => hd p)
  · intro hp d hd
    exact hp d (fun p => hd p (sectorProjection_ne_zero hn p))

theorem realResponse_sector (n : ℕ) (α β : ℝ) (p : Sector) (x : Fibre n) :
    HistoryChargeRealization.realResponse n α β (sectorSection n p x) =
      (HistoryJointChargeClassification.realWeight n α β p : ℂ) • sectorSection n p x := by
  apply PiLp.ext
  intro s
  rcases p with ⟨c, i⟩
  by_cases hs : s = i
  · subst s
    have hpp := LinearMap.congr_fun (HistoryPhaseProjection.projection_idempotent n) x
    have hrr := LinearMap.congr_fun (HistoryPhaseProjection.residual_idempotent n) x
    have hpr := LinearMap.congr_fun (HistoryPhaseProjection.projection_residual n) x
    have hrp := LinearMap.congr_fun (HistoryPhaseProjection.residual_projection n) x
    change HistoryPhaseProjection.projection n (HistoryPhaseProjection.projection n x) =
      HistoryPhaseProjection.projection n x at hpp
    change HistoryPhaseProjection.residual n (HistoryPhaseProjection.residual n x) =
      HistoryPhaseProjection.residual n x at hrr
    change HistoryPhaseProjection.projection n (HistoryPhaseProjection.residual n x) = 0 at hpr
    change HistoryPhaseProjection.residual n (HistoryPhaseProjection.projection n x) = 0 at hrp
    cases c <;>
      simp [HistoryChargeRealization.realResponse, blocks_apply,
        HistoryChargeRealization.realComponent, HistoryRelativePhase.block_apply,
        sectorSection_apply, phaseProjection, hpp, hrr, hpr, hrp]
  · simp [HistoryChargeRealization.realResponse, blocks_apply,
      sectorSection_apply, hs]

theorem response_sector (n : ℕ) (r b : ℤ) (p : Sector) (x : Fibre n) :
    response n r b (sectorSection n p x) =
      (weight n r b p : ℂ) • sectorSection n p x := by
  rw [← HistoryChargeRealization.realResponse_integral]
  simpa [HistoryJointChargeClassification.realWeight, weight] using
    realResponse_sector n r b p x

theorem generatedResponse_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    generatedResponse n (sectorSection n p x) =
      (generatedWeight n p : ℂ) • sectorSection n p x :=
  response_sector n n 1 p x

theorem normalizedResponse_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    HistoryChargeContent.normalizedResponse n (sectorSection n p x) =
      ((generatedWeight n p : ℂ) / (2 * n)) • sectorSection n p x := by
  simp only [HistoryChargeContent.normalizedResponse, LinearMap.smul_apply,
    generatedResponse_sector, smul_smul]
  congr 1
  ring

/-- The two generators are the already constructed operators at unit
coefficients, not independent endomorphisms added to the source. -/
def relativeGenerator (n : ℕ) : Module.End ℂ (Space n) := response n 0 1

def rightGenerator (n : ℕ) : Module.End ℂ (Space n) := response n 1 0

theorem relativeGenerator_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    relativeGenerator n (sectorSection n p x) =
      (relativeWeight n p.1 : ℂ) • sectorSection n p x := by
  simpa only [relativeGenerator, weight, zero_mul, one_mul, zero_add] using
    response_sector n 0 1 p x

theorem rightGenerator_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    rightGenerator n (sectorSection n p x) =
      (rightWeight p.2 : ℂ) • sectorSection n p x := by
  simpa only [rightGenerator, weight, zero_mul, one_mul, add_zero] using
    response_sector n 1 0 p x

theorem response_generators (n : ℕ) (r b : ℤ) :
    response n r b = (r : ℂ) • rightGenerator n + (b : ℂ) • relativeGenerator n := by
  have he : ∀ p x, response n r b (sectorSection n p x) =
      ((r : ℂ) • rightGenerator n + (b : ℂ) • relativeGenerator n) (sectorSection n p x) := by
    intro p x
    simp only [response_sector, LinearMap.add_apply, LinearMap.smul_apply,
      relativeGenerator_sector, rightGenerator_sector, smul_smul, ← add_smul]
    congr 1
    push_cast [weight]
    ring
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (sectorProjection_sum n) x
  change (∑ p : Sector, sectorProjection n p x) = x at hx
  rw [← hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact he p (x p.2)

theorem generatedResponse_generators (n : ℕ) :
    generatedResponse n = (n : ℂ) • rightGenerator n + relativeGenerator n := by
  simpa only [generatedResponse, Int.cast_natCast, Int.cast_one, one_smul] using
    response_generators n n 1

def responseWeight (n : ℕ) (p : Sector) : ℝ :=
  (if p.1 then HistoryDetailCasimir.coefficient n else 0) +
    ((generatedWeight n p : ℝ) / (2 * n)) ^ 2

theorem responseWeight_nonneg (n : ℕ) (p : Sector) : 0 ≤ responseWeight n p := by
  apply add_nonneg _ (sq_nonneg _)
  exact ite_nonneg (HistoryDetailCasimir.coefficient_nonneg n) le_rfl

theorem responseWeight_zero_iff {n : ℕ} (hn : 2 ≤ n) (p : Sector) :
    responseWeight n p = 0 ↔ p = (false, .inr 0) := by
  constructor
  · intro hz
    have hd : 0 ≤ (if p.1 then HistoryDetailCasimir.coefficient n else 0) :=
      ite_nonneg (HistoryDetailCasimir.coefficient_nonneg n) le_rfl
    have hs : ((generatedWeight n p : ℝ) / (2 * n)) ^ 2 = 0 := by
      unfold responseWeight at hz
      nlinarith [sq_nonneg ((generatedWeight n p : ℝ) / (2 * n))]
    have he := (sq_eq_zero_iff.mp hs)
    have hden : (2 * n : ℝ) ≠ 0 := by positivity
    have hw : generatedWeight n p = 0 := by
      exact_mod_cast (div_eq_zero_iff.mp he).resolve_right hden
    exact (generated_zero_iff hn p).mp hw
  · rintro rfl
    simp [responseWeight, generatedWeight, weight, rightWeight, relativeWeight]

theorem detailResponse_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    HistoryChargedCasimirResponse.detailResponse n (sectorSection n p x) =
      (if p.1 then (HistoryDetailCasimir.coefficient n : ℂ) else 0) •
        sectorSection n p x := by
  apply PiLp.ext
  intro s
  rcases p with ⟨c, i⟩
  by_cases hs : s = i
  · subst s
    have hrr := LinearMap.congr_fun (HistoryPhaseProjection.residual_idempotent n) x
    have hrp := LinearMap.congr_fun (HistoryPhaseProjection.residual_projection n) x
    cases c <;> simp_all [HistoryChargedCasimirResponse.detailResponse,
      blocks_apply, HistoryDetailCasimir.response_eq, LinearMap.smul_apply,
      sectorSection_apply, phaseProjection, Module.End.mul_apply]
  · cases c <;> simp [HistoryChargedCasimirResponse.detailResponse, blocks_apply,
      sectorSection_apply, hs]

theorem completeResponse_sector (n : ℕ) (p : Sector) (x : Fibre n) :
    HistoryChargedCasimirResponse.response n (sectorSection n p x) =
      (responseWeight n p : ℂ) • sectorSection n p x := by
  simp only [HistoryChargedCasimirResponse.response, LinearMap.add_apply,
    detailResponse_sector, HistoryChargedCasimirResponse.chargeSquare,
    HistoryJointQuadraticResponse.normalizedResponse_adjoint, Module.End.mul_apply,
    normalizedResponse_sector, map_smul, smul_smul, ← add_smul]
  congr 1
  simp only [responseWeight, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast, apply_ite, Complex.ofReal_zero]
  ring

structure Conclusions : Prop where
  complete_decomposition : ∀ n, ∑ p : Sector, sectorProjection n p = 1
  actual_projection : ∀ n p, IsIdempotentElem (sectorProjection n p)
  actual_sector_rank : ∀ n p,
    Module.finrank ℂ (LinearMap.range (sectorProjection n p)) =
      if p.1 then n * HistoryChargeContent.historyCount n
      else HistoryChargeContent.historyCount n
  real_charge_action : ∀ n α β p x,
    HistoryChargeRealization.realResponse n α β (sectorSection n p x) =
      (HistoryJointChargeClassification.realWeight n α β p : ℂ) • sectorSection n p x
  generated_charge_action : ∀ n p x,
    generatedResponse n (sectorSection n p x) =
      (generatedWeight n p : ℂ) • sectorSection n p x
  complete_response_action : ∀ n p x,
    HistoryChargedCasimirResponse.response n (sectorSection n p x) =
      (responseWeight n p : ℂ) • sectorSection n p x

theorem generated : Conclusions where
  complete_decomposition := sectorProjection_sum
  actual_projection := sectorProjection_idempotent
  actual_sector_rank := sectorProjection_finrank
  real_charge_action := realResponse_sector
  generated_charge_action := generatedResponse_sector
  complete_response_action := completeResponse_sector

end GeneratedFoundations.Arithmetic.HistoryChargeSectors
