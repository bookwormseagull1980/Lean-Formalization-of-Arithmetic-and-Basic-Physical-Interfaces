module

public import GeneratedFoundations.Arithmetic.HistoryJointChargeClassification
public import GeneratedFoundations.Arithmetic.HistoryChargedCasimirResponse

/-!
# Real charge comparisons on the actual arithmetic carrier

The real weight classification is realized here as an operator on every
retained history and source coordinate. Integral weights recover the
previous integer operator exactly. The upper invariant sector retains an
arbitrary history function; its annihilation condition is tested on the
entire subspace, not used to discard that subspace in favour of one vector.

The primitive, positive-orientation and fixed-sector properties specify
the class of competing charge formulas. They are checked for the canonical
formula, whose coefficients are already determined by the phase ranks.
The comparison theorem has no free charge coefficient at the source entry.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryChargeRealization

open HistoryJointCharge HistoryJointChargeLattice
open HistoryJointChargeClassification
open HistoryPhaseProjection (projection residual lift)

def realComponent (n : ℕ) (α β : ℝ) (s : Spin) : Module.End ℂ (Fibre n) :=
  HistoryRelativePhase.block n
    ((realWeight n α β (false, s) : ℂ), (realWeight n α β (true, s) : ℂ))

def realResponse (n : ℕ) (α β : ℝ) : Module.End ℂ (Space n) :=
  blocks n (realComponent n α β)

theorem realResponse_integral (n : ℕ) (r b : ℤ) :
    realResponse n (r : ℝ) (b : ℝ) = response n r b := by
  unfold realResponse response
  apply congrArg (blocks n)
  funext s
  unfold realComponent component
  apply congrArg (HistoryRelativePhase.block n)
  apply Prod.ext <;> simp [realWeight, weight]

theorem realComponent_symmetric (n : ℕ) (α β : ℝ) (s : Spin) (x y : Fibre n) :
    inner ℂ (realComponent n α β s x) y = inner ℂ x (realComponent n α β s y) := by
  simp only [realComponent, HistoryRelativePhase.block_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  congr 1
  · congr 1
    simpa only [HistoryPhaseProjection.projection_adjoint] using
      LinearMap.adjoint_inner_left (projection n) y x
  · congr 1
    simpa only [HistoryChargedReconstruction.residual_adjoint] using
      LinearMap.adjoint_inner_left (residual n) y x

theorem realResponse_adjoint (n : ℕ) (α β : ℝ) :
    (realResponse n α β).adjoint = realResponse n α β := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change (∑ s : Spin, inner ℂ (realResponse n α β x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (realResponse n α β y s)
  exact Finset.sum_congr rfl fun s _ => by
    simpa only [realResponse, blocks_apply] using
      realComponent_symmetric n α β s (x s) (y s)

theorem realResponse_trace (n : ℕ) (α β : ℝ) :
    LinearMap.trace ℂ (Space n) (realResponse n α β) = 0 := by
  rw [realResponse, blocks_trace]
  simp only [realComponent, HistoryJointChargeQuotient.phaseBlock_trace,
    Fintype.sum_sum_type, Fin.sum_univ_two]
  simp [realWeight, rightWeight, relativeWeight]
  ring

theorem realResponse_energy (n : ℕ) (α β : ℝ) (x : Space n) :
    ‖realResponse n α β x‖ ^ 2 = ∑ s,
      (realWeight n α β (false, s) ^ 2 * ‖projection n (x s)‖ ^ 2 +
        realWeight n α β (true, s) ^ 2 * ‖residual n (x s)‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro s _
  rw [realResponse, blocks_apply, realComponent, HistoryRelativePhase.block_apply,
    norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_left, inner_smul_right,
    HistoryPhaseProjection.projection_residual_inner, norm_smul,
    mul_zero, map_zero, add_zero, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- Every invariant history coefficient is retained in this injection. -/
def upperSection (n : ℕ) : HistoryPhaseProjection.HistorySpace n →ₗ[ℂ] Space n :=
  (inclusion n (.inr 0)).comp (lift n)

theorem upperSection_injective (n : ℕ) : Function.Injective (upperSection n) := by
  intro f g hfg
  funext h
  exact congrArg (fun x : Space n => x (.inr 0) (h, 0)) hfg

theorem realResponse_upperSection (n : ℕ) (α β : ℝ)
    (f : HistoryPhaseProjection.HistorySpace n) :
    realResponse n α β (upperSection n f) =
      (realWeight n α β (false, .inr 0) : ℂ) • upperSection n f := by
  have hp : projection n (lift n f) = lift n f := by
    change (lift n).comp ((HistoryPhaseProjection.average n).comp (lift n)) f = _
    rw [HistoryPhaseProjection.average_lift]
    rfl
  have hr : residual n (lift n f) = 0 := by
    simp [HistoryPhaseProjection.residual, hp]
  apply PiLp.ext
  intro s
  by_cases hs : s = (.inr 0 : Spin)
  · subst s
    simp [realResponse, blocks_apply, realComponent, HistoryRelativePhase.block_apply,
      upperSection, inclusion, hp, hr]
  · simp [realResponse, blocks_apply, realComponent, HistoryRelativePhase.block_apply,
      upperSection, inclusion, hs]

theorem realResponse_annihilates_upper_iff (n : ℕ) (α β : ℝ) :
    (∀ f, realResponse n α β (upperSection n f) = 0) ↔
      realWeight n α β (false, .inr 0) = 0 := by
  constructor
  · intro hz
    have h := hz (fun _ => 1)
    rw [realResponse_upperSection] at h
    have hne : upperSection n (fun _ => 1) ≠ 0 := by
      intro h0
      have hf := upperSection_injective n (h0.trans (map_zero (upperSection n)).symm)
      obtain ⟨a⟩ := (inferInstance : Nonempty (CompleteHistory.History (n + 1)))
      have he := congrFun hf a
      norm_num at he
    exact Complex.ofReal_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hne)
  · intro hz f
    rw [realResponse_upperSection, hz, Complex.ofReal_zero, zero_smul]

theorem realResponse_oriented_unique {n : ℕ} {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization n α β w) (hp : PrimitiveWeights w)
    (hv : realWeight n α β (false, .inr 0) = 0) (hβ : 0 < β) :
    realResponse n α β = generatedResponse n := by
  obtain ⟨ha, hb, _⟩ := oriented_real_vacuum_unique hw hp hv hβ
  rw [ha, hb]
  convert realResponse_integral n (n : ℤ) 1 using 1 <;> simp [generatedResponse]

theorem realResponse_unique_of_upper {n : ℕ} {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization n α β w) (hp : PrimitiveWeights w)
    (hv : ∀ f, realResponse n α β (upperSection n f) = 0) (hβ : 0 < β) :
    realResponse n α β = generatedResponse n :=
  realResponse_oriented_unique hw hp
    ((realResponse_annihilates_upper_iff n α β).mp hv) hβ

theorem generated_upper_zero (n : ℕ) (f : HistoryPhaseProjection.HistorySpace n) :
    generatedResponse n (upperSection n f) = 0 := by
  change response n n 1 (upperSection n f) = 0
  rw [← realResponse_integral n (n : ℤ) 1]
  have hw : realWeight n (n : ℝ) 1 (false, .inr 0) = 0 := by
    simp [realWeight, rightWeight, relativeWeight]
  simpa only [Int.cast_natCast, Int.cast_one] using
    (realResponse_annihilates_upper_iff n n 1).mpr hw f

structure Conclusions : Prop where
  integral_realization : ∀ n (r b : ℤ),
    realResponse n (r : ℝ) (b : ℝ) = response n r b
  actual_adjoint : ∀ n α β, (realResponse n α β).adjoint = realResponse n α β
  complete_trace : ∀ n α β, LinearMap.trace ℂ (Space n) (realResponse n α β) = 0
  retained_histories : ∀ n, Function.Injective (upperSection n)
  canonical_annihilation : ∀ n f, generatedResponse n (upperSection n f) = 0
  actual_unique_response : ∀ n α β w, IntegralRealization n α β w →
    PrimitiveWeights w → (∀ f, realResponse n α β (upperSection n f) = 0) →
    0 < β → realResponse n α β = generatedResponse n

theorem generated : Conclusions where
  integral_realization := realResponse_integral
  actual_adjoint := realResponse_adjoint
  complete_trace := realResponse_trace
  retained_histories := upperSection_injective
  canonical_annihilation := generated_upper_zero
  actual_unique_response := fun _ _ _ _ => realResponse_unique_of_upper

end GeneratedFoundations.Arithmetic.HistoryChargeRealization
