module

public import GeneratedFoundations.Arithmetic.HistoryChargedTransport
public import GeneratedFoundations.Operations.SourceCliffordConnector

/-!
# Source operations on the complete joint charge carrier

The original source matrices act on the four source coordinates while
retaining every arithmetic history and phase coefficient. This is the
tensor action on the same space used to compute the joint neutral kernel.
The source exchange is unitary on that full space. Its failure to preserve
the neutral kernel at positive phase rank is established on an actual
phase-invariant vector; a quotient operation is not assigned to it.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointSourceTransport

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)
open HistoryChargedTransport
open Operations.SourceCliffordConnector

def sourceAction (n : ℕ) (M : ChiralMatrix) : Module.End ℂ (Space n) where
  toFun x := WithLp.toLp 2 fun s => ∑ t : Spin, M s t • x t
  map_add' x y := by
    apply PiLp.ext
    intro s
    simp only [PiLp.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply PiLp.ext
    intro s
    simp only [PiLp.smul_apply, ← Finset.smul_sum, smul_comm (M s _) c, RingHom.id_apply]

@[simp] theorem sourceAction_apply (n : ℕ) (M : ChiralMatrix) (x : Space n) (s : Spin) :
    sourceAction n M x s = ∑ t : Spin, M s t • x t := rfl

theorem sourceAction_mul (n : ℕ) (M K : ChiralMatrix) :
    sourceAction n (M * K) = sourceAction n M * sourceAction n K := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [sourceAction_apply, Module.End.mul_apply, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem sourceAction_one (n : ℕ) : sourceAction n 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [sourceAction_apply, Matrix.one_apply]

def exchangeIndex : Spin → Spin
  | .inl i => .inr i
  | .inr i => .inl i

@[simp] theorem exchangeIndex_square (s : Spin) : exchangeIndex (exchangeIndex s) = s := by
  cases s <;> rfl

def exchange (n : ℕ) : Module.End ℂ (Space n) where
  toFun x := WithLp.toLp 2 fun s => x (exchangeIndex s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem exchange_apply (n : ℕ) (x : Space n) (s : Spin) :
    exchange n x s = x (exchangeIndex s) := rfl

/-- The exchange is the original unit-quaternion source operation. -/
theorem exchange_eq_source (n : ℕ) : exchange n = sourceAction n (clifford 1) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  cases s <;>
    simp [sourceAction_apply, clifford, map_one, Matrix.one_apply, exchangeIndex]

theorem exchange_square (n : ℕ) : exchange n * exchange n = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [Module.End.mul_apply]

theorem exchange_inner (n : ℕ) (x y : Space n) :
    inner ℂ (exchange n x) (exchange n y) = inner ℂ x y := by
  change (∑ s : Spin, inner ℂ (x (exchangeIndex s)) (y (exchangeIndex s))) = _
  change (∑ s : Spin, inner ℂ (x (exchangeIndex s)) (y (exchangeIndex s))) =
    ∑ s : Spin, inner ℂ (x s) (y s)
  simp only [Fintype.sum_sum_type, exchangeIndex]
  exact add_comm _ _

def exchangeUnitary (n : ℕ) : Space n ≃ₗᵢ[ℂ] Space n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ (Fibre n)
    { toFun := exchangeIndex
      invFun := exchangeIndex
      left_inv := exchangeIndex_square
      right_inv := exchangeIndex_square }

@[simp] theorem exchangeUnitary_apply (n : ℕ) (x : Space n) :
    exchangeUnitary n x = exchange n x := rfl

/-- The complete constant phase section, with all history values retained. -/
def constant (n : ℕ) : Fibre n := HistoryPhaseProjection.lift n (fun _ => 1)

theorem projection_constant (n : ℕ) : projection n (constant n) = constant n := by
  change (HistoryPhaseProjection.lift n)
    (((HistoryPhaseProjection.average n).comp (HistoryPhaseProjection.lift n)) (fun _ => 1)) = _
  rw [HistoryPhaseProjection.average_lift]
  rfl

theorem residual_constant (n : ℕ) : residual n (constant n) = 0 := by
  simp [HistoryPhaseProjection.residual, projection_constant]

def neutralSection (n : ℕ) : Space n := inclusion n (.inr 0) (constant n)

theorem neutralSection_ne_zero (n : ℕ) : neutralSection n ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space n => x (.inr 0)
    (HistoryModuleRepresentation.base n)) h
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

theorem neutralSection_mem (n : ℕ) : neutralSection n ∈ neutral n := by
  apply (neutral_iff n _).mpr
  intro s
  by_cases hs : s = .inr 0
  · subst s
    simp [neutralSection, inclusion, HistoryJointChargeLattice.generatedWeight,
      invariant_upper, residual_constant]
  · simp [neutralSection, inclusion, hs]

theorem exchange_neutralSection (n : ℕ) :
    exchange n (neutralSection n) = inclusion n (.inl 0) (constant n) := by
  apply PiLp.ext
  intro s
  cases s with
  | inl i =>
      by_cases hi : i = 0 <;> simp [neutralSection, exchangeIndex, inclusion, hi]
  | inr i => simp [neutralSection, exchangeIndex, inclusion]

theorem exchange_not_neutral {n : ℕ} (hn : 0 < n) :
    exchange n (neutralSection n) ∉ neutral n := by
  intro hx
  have hp := ((neutral_iff n _).mp hx (.inl 0)).1
  rw [exchange_neutralSection] at hp
  have hp' : (-(n : ℂ)) • constant n = 0 := by
    simpa [inclusion, generatedWeight, weight, rightWeight, relativeWeight,
      projection_constant] using hp
  have he := congrArg (fun v : Fibre n => v (HistoryModuleRepresentation.base n)) hp'
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  change -(n : ℂ) • (1 : ℂ) = 0 at he
  simp [hn'] at he

theorem exchange_does_not_preserve {n : ℕ} (hn : 0 < n) :
    ¬ PreservesNeutral n (exchange n) :=
  fun h => exchange_not_neutral hn (h (neutralSection_mem n))

theorem exchange_does_not_descend {n : ℕ} (hn : 0 < n) : ¬ Descends n (exchange n) := by
  rw [descends_iff]
  exact exchange_does_not_preserve hn

/-- Kernel preservation and unitary norm preservation are distinct facts.
The complete exchange remains a valid source operation before quotienting. -/
structure Conclusions : Prop where
  source_identification : ∀ n, exchange n = sourceAction n (clifford 1)
  actual_unitary : ∀ n x y, inner ℂ (exchange n x) (exchange n y) = inner ℂ x y
  actual_neutral_vector : ∀ n, neutralSection n ∈ neutral n
  exact_kernel_obstruction : ∀ n, 0 < n → ¬ PreservesNeutral n (exchange n)
  exact_descent_obstruction : ∀ n, 0 < n → ¬ Descends n (exchange n)

theorem generated : Conclusions where
  source_identification := exchange_eq_source
  actual_unitary := exchange_inner
  actual_neutral_vector := neutralSection_mem
  exact_kernel_obstruction := fun _ hn => exchange_does_not_preserve hn
  exact_descent_obstruction := fun _ hn => exchange_does_not_descend hn

end GeneratedFoundations.Arithmetic.HistoryJointSourceTransport
