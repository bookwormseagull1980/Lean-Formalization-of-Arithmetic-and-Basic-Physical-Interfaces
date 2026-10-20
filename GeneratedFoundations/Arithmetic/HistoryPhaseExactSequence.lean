module

public import GeneratedFoundations.Arithmetic.HistoryPhaseBundle
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The exact phase quotient of the complete generated fibre

The actual finite phase average determines two complementary linear parts:
phase-invariant observations and zero-average phase detail. The quotient by
the invariant part is canonically the retained zero-average part. Its
universal property concerns exactly the responses annihilating the invariant
part. No fibre or neutral direction is supplied to this construction.

The dimensions are computed from the generated history count and the order
of its actual finite phase kernel. In particular the physical matter counts
do not enter these arithmetic dimensions. The weighted energy identity is
the already proved identity for the same history--phase probability law.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryPhaseExactSequence

open CompleteHistory HistoryPhaseBundle

abbrev Space (n : ℕ) := Fiber n → ℝ
abbrev HistorySpace (n : ℕ) := History (n + 1) → ℝ

def lift (n : ℕ) : HistorySpace n →ₗ[ℝ] Space n where
  toFun g x := g x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def average (n : ℕ) : Space n →ₗ[ℝ] HistorySpace n where
  toFun := phaseAverage
  map_add' f g := by ext h; simp [phaseAverage, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    ext h
    simp only [phaseAverage, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl

theorem average_lift (n : ℕ) : (average n).comp (lift n) = 1 := by
  ext g h
  change phaseAverage (fun x : Fiber n => g x.1) h = g h
  exact phaseAverage_of_invariant _ (fun _ _ => rfl) (h, 0)

theorem lift_injective (n : ℕ) : Function.Injective (lift n) := by
  intro f g hfg
  ext h
  exact congrFun hfg (h, 0)

def projection (n : ℕ) : Module.End ℝ (Space n) := (lift n).comp (average n)
def residual (n : ℕ) : Module.End ℝ (Space n) := 1 - projection n

@[simp] theorem projection_apply (n : ℕ) (f : Space n) :
    projection n f = phaseProjection f := rfl

@[simp] theorem residual_apply (n : ℕ) (f : Space n) :
    residual n f = phaseResidual f := rfl

def invariant (n : ℕ) : Submodule ℝ (Space n) := LinearMap.range (lift n)
def zeroMean (n : ℕ) : Submodule ℝ (Space n) := LinearMap.ker (average n)

theorem mem_invariant_iff (n : ℕ) (f : Space n) :
    f ∈ invariant n ↔ PhaseInvariant f := by
  constructor
  · rintro ⟨g, rfl⟩ q x
    rfl
  · intro hf
    obtain ⟨g, hg, _⟩ := invariant_factorization f hf
    exact ⟨g, (funext hg).symm⟩

theorem ker_residual (n : ℕ) : LinearMap.ker (residual n) = invariant n := by
  ext f
  change phaseResidual f = 0 ↔ f ∈ invariant n
  rw [residual_zero_iff, mem_invariant_iff]

def retained (n : ℕ) : Space n →ₗ[ℝ] zeroMean n :=
  (residual n).codRestrict (zeroMean n) fun f => phaseAverage_residual f

@[simp] theorem retained_apply (n : ℕ) (f : Space n) :
    (retained n f : Space n) = phaseResidual f := rfl

theorem retained_of_zeroMean (n : ℕ) (f : zeroMean n) : retained n f = f := by
  apply Subtype.ext
  ext x
  change f.val x - phaseAverage f.val x.1 = f.val x
  have hf : phaseAverage f.val = 0 := f.property
  rw [hf]
  exact sub_zero _

theorem retained_surjective (n : ℕ) : Function.Surjective (retained n) :=
  fun f => ⟨f, retained_of_zeroMean n f⟩

theorem ker_retained (n : ℕ) : LinearMap.ker (retained n) = invariant n := by
  ext f
  change retained n f = 0 ↔ f ∈ invariant n
  rw [← ker_residual n]
  constructor
  · intro hf
    exact congrArg (fun x : zeroMean n => (x : Space n)) hf
  · intro hf
    exact Subtype.ext hf

def inclusion (n : ℕ) : invariant n →ₗ[ℝ] Space n := (invariant n).subtype
abbrev Quotient (n : ℕ) := Space n ⧸ invariant n
def quotient (n : ℕ) : Space n →ₗ[ℝ] Quotient n := (invariant n).mkQ

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion n) :=
  fun _ _ h => Subtype.ext h

theorem quotient_surjective (n : ℕ) : Function.Surjective (quotient n) :=
  (invariant n).mkQ_surjective

theorem invariant_complete_quotient_exact (n : ℕ) :
    Function.Exact (inclusion n) (quotient n) :=
  LinearMap.exact_subtype_mkQ (invariant n)

theorem quotient_inclusion_zero (n : ℕ) :
    (quotient n).comp (inclusion n) = 0 :=
  (invariant_complete_quotient_exact n).linearMap_comp_eq_zero

/-- Every quotient class keeps its unique zero-average representative. -/
def quotientRetained (n : ℕ) : Quotient n ≃ₗ[ℝ] zeroMean n :=
  (Submodule.quotEquivOfEq _ _ (ker_retained n).symm).trans
    ((retained n).quotKerEquivOfSurjective (retained_surjective n))

theorem quotientRetained_apply (n : ℕ) (f : Space n) :
    quotientRetained n (quotient n f) = retained n f := by
  rfl

theorem full_reconstruction (n : ℕ) (f : Space n) :
    lift n (average n f) + (quotientRetained n (quotient n f) : Space n) = f := by
  ext x
  change phaseProjection f x + (f x - phaseProjection f x) = f x
  ring

def invariantCoordinates (n : ℕ) : HistorySpace n ≃ₗ[ℝ] invariant n :=
  LinearEquiv.ofInjective (lift n) (lift_injective n)

theorem invariant_finrank (n : ℕ) :
    Module.finrank ℝ (invariant n) = Fintype.card (History (n + 1)) := by
  rw [← (invariantCoordinates n).finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem space_finrank (n : ℕ) :
    Module.finrank ℝ (Space n) = Fintype.card (History (n + 1)) * (n + 1) := by
  simp [Space, Fiber, CompleteNaturalObject.CompleteFiber, Module.finrank_fintype_fun_eq_card]

theorem quotient_finrank (n : ℕ) :
    Module.finrank ℝ (Quotient n) = Fintype.card (History (n + 1)) * n := by
  have h := (invariant n).finrank_quotient_add_finrank
  rw [invariant_finrank, space_finrank, Nat.mul_add, Nat.mul_one] at h
  exact Nat.add_right_cancel h

theorem zeroMean_finrank (n : ℕ) :
    Module.finrank ℝ (zeroMean n) = Fintype.card (History (n + 1)) * n := by
  rw [← (quotientRetained n).finrank_eq, quotient_finrank]

def descend {W : Type*} [AddCommGroup W] [Module ℝ W] (n : ℕ)
    (f : Space n →ₗ[ℝ] W) (hf : invariant n ≤ LinearMap.ker f) :
    Quotient n →ₗ[ℝ] W := (invariant n).liftQ f hf

theorem descend_comp {W : Type*} [AddCommGroup W] [Module ℝ W] (n : ℕ)
    (f : Space n →ₗ[ℝ] W) (hf : invariant n ≤ LinearMap.ker f) :
    (descend n f hf).comp (quotient n) = f :=
  Submodule.liftQ_mkQ _ _ _

theorem descend_existsUnique {W : Type*} [AddCommGroup W] [Module ℝ W] (n : ℕ)
    (f : Space n →ₗ[ℝ] W) (hf : invariant n ≤ LinearMap.ker f) :
    ∃! g : Quotient n →ₗ[ℝ] W, g.comp (quotient n) = f := by
  refine ⟨descend n f hf, descend_comp n f hf, ?_⟩
  intro g hg
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := quotient_surjective n q
  exact (LinearMap.congr_fun hg x).trans
    (LinearMap.congr_fun (descend_comp n f hf).symm x)

theorem retained_energy (n : ℕ) (f : Space n) :
    energy f = energy (projection n f) +
      energy (quotientRetained n (quotient n f) : Space n) :=
  energy_decomposition f

structure Conclusions : Prop where
  middle_exact : ∀ n, Function.Exact (inclusion n) (quotient n)
  effective_quotient : ∀ n, Function.Bijective (quotientRetained n)
  complete_reconstruction : ∀ n (f : Space n),
    lift n (average n f) + (quotientRetained n (quotient n f) : Space n) = f
  actual_dimension : ∀ n,
    Module.finrank ℝ (Quotient n) = Fintype.card (History (n + 1)) * n
  exact_weighted_energy : ∀ n (f : Space n),
    energy f = energy (projection n f) +
      energy (quotientRetained n (quotient n f) : Space n)

theorem generated : Conclusions where
  middle_exact := invariant_complete_quotient_exact
  effective_quotient := fun n => (quotientRetained n).bijective
  complete_reconstruction := full_reconstruction
  actual_dimension := quotient_finrank
  exact_weighted_energy := retained_energy

end GeneratedFoundations.Arithmetic.HistoryPhaseExactSequence
