module

public import GeneratedFoundations.Arithmetic.HistoryJointSourceTransport
public import GeneratedFoundations.Arithmetic.HistoryChargeContent
public import GeneratedFoundations.Operations.SourceCliffordComplex

/-!
# Elementary connectors on the actual joint charge carrier

The source odd response is applied on the same four-coordinate Hilbert
space used to construct the full arithmetic neutral kernel. Every history
and phase coefficient is retained. On a nonzero invariant neutral section,
a nonzero doublet has a nonzero left image, which is not neutral at positive
phase rank. Its failure to descend is therefore established for the actual
scalar connector, rather than inferred from the exchange operation alone.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate

namespace GeneratedFoundations.Arithmetic.HistoryJointConnector

open HistoryJointCharge HistoryJointChargeLattice HistoryJointSourceTransport
open HistoryChargedTransport
open Operations
open SourceCliffordConnector (ChiralMatrix)
open ReversalRealConnector (Spinor connectorOfDoublet)

theorem sourceAction_zero (n : ℕ) : sourceAction n 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [sourceAction_apply]

theorem sourceAction_add (n : ℕ) (M K : ChiralMatrix) :
    sourceAction n (M + K) = sourceAction n M + sourceAction n K := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [sourceAction_apply, add_smul, Finset.sum_add_distrib]

theorem sourceAction_inner (n : ℕ) (M : ChiralMatrix) (x y : Space n) :
    inner ℂ (sourceAction n M x) y = inner ℂ x (sourceAction n M.conjTranspose y) := by
  change (∑ s : Spin, inner ℂ (∑ t : Spin, M s t • x t) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (∑ t : Spin, M.conjTranspose s t • y t)
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

def scalarConnector (n : ℕ) (H : Spinor) : Module.End ℂ (Space n) :=
  sourceAction n (SourceCliffordComplex.connector (connectorOfDoublet H))

@[simp] theorem scalarConnector_zero (n : ℕ) : scalarConnector n 0 = 0 := by
  have hz : connectorOfDoublet 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [connectorOfDoublet]
  rw [scalarConnector, hz]
  simpa [SourceCliffordComplex.connector] using sourceAction_zero n

theorem scalarConnector_adjoint (n : ℕ) (H : Spinor) :
    (scalarConnector n H).adjoint = scalarConnector n H := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simpa only [scalarConnector, SourceCliffordComplex.connector_adjoint] using
    sourceAction_inner n (SourceCliffordComplex.connector (connectorOfDoublet H)) x y

def grading (n : ℕ) : Module.End ℂ (Space n) :=
  sourceAction n SourceCliffordConnector.grading

theorem scalarConnector_odd (n : ℕ) (H : Spinor) :
    grading n * scalarConnector n H + scalarConnector n H * grading n = 0 := by
  rw [grading, scalarConnector, ← sourceAction_mul, ← sourceAction_mul,
    ← sourceAction_add, SourceCliffordComplex.connector_odd, sourceAction_zero]

theorem scalarConnector_neutral_left (n : ℕ) (H : Spinor) (i : Fin 2) :
    scalarConnector n H (neutralSection n) (.inl i) =
      connectorOfDoublet H i 0 • constant n := by
  simp [scalarConnector, sourceAction_apply, SourceCliffordComplex.connector,
    neutralSection, inclusion]

@[simp] theorem constant_base (n : ℕ) :
    constant n (HistoryModuleRepresentation.base n) = 1 := rfl

theorem scalarConnector_neutral_right (n : ℕ) (H : Spinor) (i : Fin 2) :
    scalarConnector n H (neutralSection n) (.inr i) = 0 := by
  simp [scalarConnector, sourceAction_apply, SourceCliffordComplex.connector,
    neutralSection, inclusion]

theorem scalarConnector_neutral_formula (n : ℕ) (H : Spinor) :
    scalarConnector n H (neutralSection n) =
      inclusion n (.inl 0) (star (H 1) • constant n) +
        inclusion n (.inl 1) (-star (H 0) • constant n) := by
  apply PiLp.ext
  intro s
  cases s with
  | inl i =>
    rw [scalarConnector_neutral_left]
    fin_cases i <;> simp [inclusion, connectorOfDoublet]
  | inr i => simp [scalarConnector_neutral_right, inclusion]

theorem scalarConnector_neutral_eq_zero_iff (n : ℕ) (H : Spinor) :
    scalarConnector n H (neutralSection n) = 0 ↔ H = 0 := by
  constructor
  · intro h
    have hz (i : Fin 2) : connectorOfDoublet H i 0 = 0 := by
      have he := congrArg (fun x : Space n => x (.inl i)
        (HistoryModuleRepresentation.base n)) h
      rw [scalarConnector_neutral_left] at he
      change connectorOfDoublet H i 0 * constant n (HistoryModuleRepresentation.base n) = 0 at he
      simpa only [constant_base, mul_one] using he
    funext i
    fin_cases i
    · simpa [connectorOfDoublet] using hz 1
    · simpa [connectorOfDoublet] using hz 0
  · rintro rfl
    simp

theorem scalarConnector_neutral_not_mem {n : ℕ} (hn : 0 < n)
    {H : Spinor} (hH : H ≠ 0) :
    scalarConnector n H (neutralSection n) ∉ neutral n := by
  intro hx
  have hn' : -(n : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn.ne')
  have hz (i : Fin 2) : connectorOfDoublet H i 0 = 0 := by
    have hp := ((neutral_iff n _).mp hx (.inl i)).1
    rw [scalarConnector_neutral_left, map_smul, projection_constant] at hp
    have he := congrArg (fun v : Fibre n => v (HistoryModuleRepresentation.base n)) hp
    have he' : -(n : ℂ) * connectorOfDoublet H i 0 = 0 := by
      simpa [generatedWeight, weight, rightWeight, relativeWeight,
        constant_base] using he
    exact (mul_eq_zero.mp he').resolve_left hn'
  apply hH
  funext i
  fin_cases i
  · simpa [connectorOfDoublet] using hz 1
  · simpa [connectorOfDoublet] using hz 0

theorem scalarConnector_not_preservesNeutral {n : ℕ} (hn : 0 < n)
    {H : Spinor} (hH : H ≠ 0) : ¬ PreservesNeutral n (scalarConnector n H) :=
  fun h => scalarConnector_neutral_not_mem hn hH (h (neutralSection_mem n))

theorem scalarConnector_descends_iff {n : ℕ} (hn : 0 < n) (H : Spinor) :
    Descends n (scalarConnector n H) ↔ H = 0 := by
  rw [descends_iff]
  constructor
  · intro h
    by_contra hH
    exact scalarConnector_not_preservesNeutral hn hH h
  · rintro rfl
    intro x _
    change scalarConnector n 0 x ∈ neutral n
    rw [scalarConnector_zero, LinearMap.zero_apply]
    exact (neutral n).zero_mem

theorem scalarConnector_not_commute {n : ℕ} (hn : 0 < n)
    {H : Spinor} (hH : H ≠ 0) :
    ¬ Commute (scalarConnector n H) (HistoryJointChargeQuotient.neutralProjection n) := by
  intro hc
  exact scalarConnector_not_preservesNeutral hn hH
    ((selfAdjoint_preserves_iff_commutes n _ (scalarConnector_adjoint n H)).mpr hc.eq)

/-- Descent preserves the entire calculated neutral kernel, not just its
constant section. This criterion does not require self-adjointness. -/
theorem preservesNeutral_iff_projection (n : ℕ) (A : Module.End ℂ (Space n)) :
    PreservesNeutral n A ↔
      HistoryJointChargeQuotient.neutralProjection n * A *
        HistoryJointChargeQuotient.neutralProjection n =
      A * HistoryJointChargeQuotient.neutralProjection n := by
  constructor
  · intro hp
    apply LinearMap.ext
    intro x
    apply (HistoryJointChargeQuotient.neutralProjection_fixed_iff n _).mpr
    exact hp ((HistoryJointChargeQuotient.neutralProjection_fixed_iff n _).mp
      (LinearMap.congr_fun (HistoryJointChargeQuotient.neutralProjection_idempotent n) x))
  · intro h x hx
    apply (HistoryJointChargeQuotient.neutralProjection_fixed_iff n _).mp
    have he := LinearMap.congr_fun h x
    simp only [Module.End.mul_apply] at he
    rwa [(HistoryJointChargeQuotient.neutralProjection_fixed_iff n x).mpr hx] at he

theorem descends_iff_map_le (n : ℕ) (A : Module.End ℂ (Space n)) :
    Descends n A ↔ (neutral n).map A ≤ neutral n := by
  rw [descends_iff]
  exact Submodule.map_le_iff_le_comap.symm

theorem scalarConnector_neutral_in_left (n : ℕ) (H : Spinor) :
    HistoryChargeContent.leftProjection n (scalarConnector n H (neutralSection n)) =
      scalarConnector n H (neutralSection n) := by
  apply PiLp.ext
  intro s
  cases s with
  | inl i => simp [HistoryChargeContent.leftProjection, blocks_apply]
  | inr i => simp [HistoryChargeContent.leftProjection, blocks_apply,
      scalarConnector_neutral_right]

theorem scalarConnector_selfAdjoint_odd_not_descends {n : ℕ} (hn : 0 < n)
    {H : Spinor} (hH : H ≠ 0) :
    (scalarConnector n H).adjoint = scalarConnector n H ∧
      grading n * scalarConnector n H + scalarConnector n H * grading n = 0 ∧
      ¬ Descends n (scalarConnector n H) :=
  ⟨scalarConnector_adjoint n H, scalarConnector_odd n H,
    fun h => hH ((scalarConnector_descends_iff hn H).mp h)⟩

structure Conclusions : Prop where
  actual_neutral_image : ∀ n H,
    scalarConnector n H (neutralSection n) =
      inclusion n (.inl 0) (star (H 1) • constant n) +
        inclusion n (.inl 1) (-star (H 0) • constant n)
  self_adjoint : ∀ n H, (scalarConnector n H).adjoint = scalarConnector n H
  odd : ∀ n H, grading n * scalarConnector n H + scalarConnector n H * grading n = 0
  exact_descent : ∀ n, 0 < n → ∀ H, Descends n (scalarConnector n H) ↔ H = 0
  full_kernel_criterion : ∀ n A, PreservesNeutral n A ↔
    HistoryJointChargeQuotient.neutralProjection n * A *
      HistoryJointChargeQuotient.neutralProjection n =
    A * HistoryJointChargeQuotient.neutralProjection n

theorem generated : Conclusions where
  actual_neutral_image := scalarConnector_neutral_formula
  self_adjoint := scalarConnector_adjoint
  odd := scalarConnector_odd
  exact_descent := fun _ => scalarConnector_descends_iff
  full_kernel_criterion := preservesNeutral_iff_projection

end GeneratedFoundations.Arithmetic.HistoryJointConnector
