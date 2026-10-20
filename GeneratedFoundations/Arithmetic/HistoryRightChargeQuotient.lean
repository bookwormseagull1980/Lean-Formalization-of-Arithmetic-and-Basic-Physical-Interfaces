module

public import GeneratedFoundations.Arithmetic.HistoryJointQuadraticResponse
public import GeneratedFoundations.Arithmetic.HistoryChargeContent

/-!
# The complete neutral kernel in the right arithmetic sector

At positive phase rank the previously computed neutral kernel lies entirely
in the right sector. Restriction and inclusion give inverse linear maps on
that full kernel, retaining every history. The resulting quotient dimensions
are derived from this equivalence. Rank one keeps its extra neutral detail
component; it is not replaced by the generic-rank formula.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryRightChargeQuotient

open HistoryJointCharge HistoryJointChargeLattice HistoryJointChargeQuotient
open HistoryJointQuadraticResponse HistoryChargeContent

def rightSection (n : ℕ) : Space n →ₗ[ℂ] RightSpace n where
  toFun x := WithLp.toLp 2 fun i => x (.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rightSection_inclusion (n : ℕ) (x : RightSpace n) :
    rightSection n (rightInclusion n x) = x := by
  apply PiLp.ext
  intro i
  rfl

theorem rightProjection_formula (n : ℕ) (x : Space n) :
    rightInclusion n (rightSection n x) = x - leftProjection n x := by
  apply PiLp.ext
  intro s
  cases s <;> simp [rightSection, leftProjection, blocks_apply]
  rfl

theorem neutral_left_zero {n : ℕ} (hn : 0 < n) (x : Space n) (hx : x ∈ neutral n) :
    leftProjection n x = 0 := by
  have hp := (neutralProjection_fixed_iff n x).mpr hx
  have hz := LinearMap.congr_fun (HistoryChargeContent.left_neutral_zero hn) x
  change leftProjection n (neutralProjection n x) = 0 at hz
  rwa [hp] at hz

theorem neutral_reconstruction {n : ℕ} (hn : 0 < n) (x : Space n)
    (hx : x ∈ neutral n) : rightInclusion n (rightSection n x) = x := by
  rw [rightProjection_formula, neutral_left_zero hn x hx, sub_zero]

abbrev RightNeutral (n : ℕ) := LinearMap.ker (rightCharge n)

def rightNeutralMap (n : ℕ) : RightNeutral n →ₗ[ℂ] neutral n where
  toFun x := ⟨rightInclusion n x.val, (rightNeutral_iff n x.val).mp x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (rightInclusion n) x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (rightInclusion n) c x.val

theorem rightNeutralMap_injective (n : ℕ) : Function.Injective (rightNeutralMap n) := by
  intro x y h
  apply Subtype.ext
  exact rightInclusion_injective n (congrArg Subtype.val h)

theorem rightNeutralMap_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (rightNeutralMap n) := by
  intro y
  have hy := neutral_reconstruction hn y.val y.property
  have hm : rightSection n y.val ∈ RightNeutral n := by
    apply (rightNeutral_iff n _).mpr
    rw [hy]
    exact y.property
  refine ⟨⟨rightSection n y.val, hm⟩, ?_⟩
  apply Subtype.ext
  exact hy

def rightNeutralEquiv {n : ℕ} (hn : 0 < n) : RightNeutral n ≃ₗ[ℂ] neutral n :=
  LinearEquiv.ofBijective (rightNeutralMap n)
    ⟨rightNeutralMap_injective n, rightNeutralMap_surjective hn⟩

theorem rightSpace_finrank (n : ℕ) :
    Module.finrank ℂ (RightSpace n) = 2 * historyCount n * (n + 1) := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin 2 → Fibre n)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Fibre, HistoryModuleRepresentation.Space, historyCount]
  ring

theorem rightNeutral_finrank {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (RightNeutral n) = historyCount n := by
  have hp : 0 < n := by omega
  rw [(rightNeutralEquiv hp).finrank_eq]
  exact neutral_finrank_large hn

theorem rightChargedQuotient_finrank {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (RightSpace n ⧸ RightNeutral n) = (2 * n + 1) * historyCount n := by
  have h := (RightNeutral n).finrank_quotient_add_finrank
  rw [rightNeutral_finrank hn, rightSpace_finrank] at h
  nlinarith

theorem rightSquaredQuotient_finrank {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (RightSpace n ⧸ LinearMap.ker (rightSquaredResponse n)) =
      (2 * n + 1) * historyCount n := by
  rw [rightSquaredResponse_kernel]
  exact rightChargedQuotient_finrank hn

theorem rightNeutral_finrank_one : Module.finrank ℂ (RightNeutral 1) =
    2 * historyCount 1 := by
  rw [(rightNeutralEquiv (by decide : 0 < 1)).finrank_eq]
  exact HistoryChargedReconstruction.neutral_finrank_one

theorem rightChargedQuotient_finrank_one :
    Module.finrank ℂ (RightSpace 1 ⧸ RightNeutral 1) = 2 * historyCount 1 := by
  have h := (RightNeutral 1).finrank_quotient_add_finrank
  rw [rightNeutral_finrank_one, rightSpace_finrank] at h
  nlinarith

theorem quotient_counts_agree {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (RightSpace n ⧸ RightNeutral n) = rightChargedCount n := by
  rw [rightChargedQuotient_finrank hn, rightChargedCount_eq hn]

structure Conclusions : Prop where
  complete_neutral_equivalence : ∀ n (hn : 0 < n), Function.Bijective (rightNeutralEquiv hn)
  right_dimension : ∀ n,
    Module.finrank ℂ (RightSpace n) = 2 * historyCount n * (n + 1)
  actual_neutral_rank : ∀ n, 2 ≤ n → Module.finrank ℂ (RightNeutral n) = historyCount n
  actual_quotient_rank : ∀ n, 2 ≤ n →
    Module.finrank ℂ (RightSpace n ⧸ RightNeutral n) = (2 * n + 1) * historyCount n
  quadratic_quotient_rank : ∀ n, 2 ≤ n →
    Module.finrank ℂ (RightSpace n ⧸ LinearMap.ker (rightSquaredResponse n)) =
      (2 * n + 1) * historyCount n
  small_neutral_rank : Module.finrank ℂ (RightNeutral 1) = 2 * historyCount 1
  small_quotient_rank : Module.finrank ℂ (RightSpace 1 ⧸ RightNeutral 1) = 2 * historyCount 1
  content_agreement : ∀ n, 2 ≤ n →
    Module.finrank ℂ (RightSpace n ⧸ RightNeutral n) = rightChargedCount n

theorem generated : Conclusions where
  complete_neutral_equivalence := fun _ hn => (rightNeutralEquiv hn).bijective
  right_dimension := rightSpace_finrank
  actual_neutral_rank := fun _ => rightNeutral_finrank
  actual_quotient_rank := fun _ => rightChargedQuotient_finrank
  quadratic_quotient_rank := fun _ => rightSquaredQuotient_finrank
  small_neutral_rank := rightNeutral_finrank_one
  small_quotient_rank := rightChargedQuotient_finrank_one
  content_agreement := fun _ => quotient_counts_agree

end GeneratedFoundations.Arithmetic.HistoryRightChargeQuotient
