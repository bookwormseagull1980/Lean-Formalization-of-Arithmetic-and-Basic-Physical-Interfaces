module

public import GeneratedFoundations.Arithmetic.HistoryChargedReconstruction

/-!
# Actual transport and quotient descent of the joint charge carrier

Descent is the universal property of the computed full neutral kernel.
The generated finite phase action preserves that kernel and hence acts on
the quotient. This is proved on vectors before passage to the quotient.
Preservation of a kernel is distinguished from orthogonal compression;
an arbitrary full response need not preserve it.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryChargedTransport

open HistoryJointCharge HistoryJointChargeLattice HistoryJointChargeQuotient
open HistoryChargedReconstruction

def quotientMap (n : ℕ) : Space n →ₗ[ℂ] Quotient n := (neutral n).mkQ

theorem quotientMap_surjective (n : ℕ) : Function.Surjective (quotientMap n) :=
  (neutral n).mkQ_surjective

theorem quotientMap_eq_zero_iff (n : ℕ) (x : Space n) :
    quotientMap n x = 0 ↔ x ∈ neutral n := by
  change x ∈ LinearMap.ker (neutral n).mkQ ↔ _
  rw [Submodule.ker_mkQ]

def PreservesNeutral (n : ℕ) (A : Module.End ℂ (Space n)) : Prop :=
  neutral n ≤ (neutral n).comap A

def Descends (n : ℕ) (A : Module.End ℂ (Space n)) : Prop :=
  ∃ B : Module.End ℂ (Quotient n), (quotientMap n).comp A = B.comp (quotientMap n)

def induced (n : ℕ) (A : Module.End ℂ (Space n)) (hA : PreservesNeutral n A) :
    Module.End ℂ (Quotient n) := (neutral n).mapQ (neutral n) A hA

@[simp] theorem induced_apply (n : ℕ) (A : Module.End ℂ (Space n))
    (hA : PreservesNeutral n A) (x : Space n) :
    induced n A hA (quotientMap n x) = quotientMap n (A x) := rfl

theorem induced_intertwines (n : ℕ) (A : Module.End ℂ (Space n))
    (hA : PreservesNeutral n A) :
    (quotientMap n).comp A = (induced n A hA).comp (quotientMap n) := by
  ext x
  rfl

theorem preserves_of_intertwines (n : ℕ) (A : Module.End ℂ (Space n))
    (B : Module.End ℂ (Quotient n))
    (h : (quotientMap n).comp A = B.comp (quotientMap n)) : PreservesNeutral n A := by
  intro x hx
  change A x ∈ neutral n
  apply (quotientMap_eq_zero_iff n (A x)).mp
  have hx0 := (quotientMap_eq_zero_iff n x).mpr hx
  have he := LinearMap.congr_fun h x
  change quotientMap n (A x) = B (quotientMap n x) at he
  rw [hx0, map_zero] at he
  exact he

theorem descends_iff (n : ℕ) (A : Module.End ℂ (Space n)) :
    Descends n A ↔ PreservesNeutral n A := by
  constructor
  · rintro ⟨B, hB⟩
    exact preserves_of_intertwines n A B hB
  · intro hA
    exact ⟨induced n A hA, induced_intertwines n A hA⟩

theorem induced_unique (n : ℕ) (A : Module.End ℂ (Space n)) (hA : PreservesNeutral n A)
    (B : Module.End ℂ (Quotient n))
    (hB : (quotientMap n).comp A = B.comp (quotientMap n)) : B = induced n A hA := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := quotientMap_surjective n q
  exact (LinearMap.congr_fun hB x).symm

theorem existsUnique_induced_iff (n : ℕ) (A : Module.End ℂ (Space n)) :
    (∃! B : Module.End ℂ (Quotient n),
      (quotientMap n).comp A = B.comp (quotientMap n)) ↔ PreservesNeutral n A := by
  constructor
  · rintro ⟨B, hB, _⟩
    exact preserves_of_intertwines n A B hB
  · intro hA
    exact ⟨induced n A hA, induced_intertwines n A hA, induced_unique n A hA⟩

theorem preservesNeutral_of_commutes (n : ℕ) (A : Module.End ℂ (Space n))
    (hA : A * neutralProjection n = neutralProjection n * A) : PreservesNeutral n A := by
  intro x hx
  apply (neutralProjection_fixed_iff n (A x)).mp
  have he := LinearMap.congr_fun hA x
  change A (neutralProjection n x) = neutralProjection n (A x) at he
  rw [(neutralProjection_fixed_iff n x).mpr hx] at he
  exact he.symm

theorem selfAdjoint_preserves_iff_commutes (n : ℕ) (A : Module.End ℂ (Space n))
    (hA : A.adjoint = A) : PreservesNeutral n A ↔
      A * neutralProjection n = neutralProjection n * A := by
  constructor
  · intro hp
    have he : neutralProjection n * A * neutralProjection n = A * neutralProjection n := by
      apply LinearMap.ext
      intro x
      apply (neutralProjection_fixed_iff n _).mpr
      exact hp ((neutralProjection_fixed_iff n _).mp
        (LinearMap.congr_fun (neutralProjection_idempotent n) x))
    have ht := congrArg LinearMap.adjoint he
    simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hA,
      neutralProjection_adjoint] at ht
    have ht' : neutralProjection n * A * neutralProjection n = neutralProjection n * A := by
      simpa only [Module.End.mul_eq_comp, LinearMap.comp_assoc] using ht
    exact he.symm.trans ht'
  · exact preservesNeutral_of_commutes n A

def phaseTransport (n : ℕ) (q : ZMod (n + 1)) : Module.End ℂ (Space n) :=
  blocks n (fun _ => (HistoryPhaseAction.unitary n q).toLinearEquiv.toLinearMap)

@[simp] theorem phaseTransport_apply (n : ℕ) (q : ZMod (n + 1))
    (x : Space n) (s : Spin) : phaseTransport n q x s = HistoryPhaseAction.unitary n q (x s) :=
  blocks_apply n _ x s

theorem phaseTransport_zero (n : ℕ) : phaseTransport n 0 = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simpa only [phaseTransport_apply, Module.End.one_apply] using
    HistoryPhaseAction.unitary_zero n (x s)

theorem phaseTransport_add (n : ℕ) (p q : ZMod (n + 1)) :
    phaseTransport n (p + q) = phaseTransport n p * phaseTransport n q := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simpa only [Module.End.mul_apply, phaseTransport_apply] using
    (HistoryPhaseAction.unitary_add n p q (x s)).symm

theorem phaseTransport_inner (n : ℕ) (q : ZMod (n + 1)) (x y : Space n) :
    inner ℂ (phaseTransport n q x) (phaseTransport n q y) = inner ℂ x y := by
  change (∑ s : Spin, inner ℂ (phaseTransport n q x s) (phaseTransport n q y s)) = _
  simp only [phaseTransport_apply, HistoryPhaseAction.unitary_inner]
  rfl

theorem phaseTransport_commutes (n : ℕ) (q : ZMod (n + 1)) :
    phaseTransport n q * neutralProjection n = neutralProjection n * phaseTransport n q := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [Module.End.mul_apply, phaseTransport_apply, neutralProjection,
    blocks_apply, neutralComponent, HistoryRelativePhase.block_apply]
  simp [HistoryPhaseProjection.residual, HistoryPhaseProjection.translation_projection,
    HistoryPhaseProjection.projection_translation]

theorem phase_preservesNeutral (n : ℕ) (q : ZMod (n + 1)) :
    PreservesNeutral n (phaseTransport n q) :=
  preservesNeutral_of_commutes n _ (phaseTransport_commutes n q)

def quotientPhase (n : ℕ) (q : ZMod (n + 1)) : Module.End ℂ (Quotient n) :=
  induced n (phaseTransport n q) (phase_preservesNeutral n q)

theorem quotientPhase_zero (n : ℕ) : quotientPhase n 0 = 1 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := quotientMap_surjective n q
  change quotientMap n (phaseTransport n 0 x) = quotientMap n x
  rw [phaseTransport_zero]
  rfl

theorem quotientPhase_add (n : ℕ) (p q : ZMod (n + 1)) :
    quotientPhase n (p + q) = quotientPhase n p * quotientPhase n q := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := quotientMap_surjective n z
  change quotientMap n (phaseTransport n (p + q) x) =
    quotientMap n (phaseTransport n p (phaseTransport n q x))
  rw [phaseTransport_add]
  rfl

structure Conclusions : Prop where
  exact_descent : ∀ n A, Descends n A ↔ PreservesNeutral n A
  unique_descent : ∀ n A, (∃! B : Module.End ℂ (HistoryChargedReconstruction.Quotient n),
    (quotientMap n).comp A = B.comp (quotientMap n)) ↔ PreservesNeutral n A
  actual_phase_invariance : ∀ n q, PreservesNeutral n (phaseTransport n q)
  full_phase_inner : ∀ n q x y,
    inner ℂ (phaseTransport n q x) (phaseTransport n q y) = inner ℂ x y
  quotient_composition : ∀ n p q,
    quotientPhase n (p + q) = quotientPhase n p * quotientPhase n q

theorem generated : Conclusions where
  exact_descent := descends_iff
  unique_descent := existsUnique_induced_iff
  actual_phase_invariance := phase_preservesNeutral
  full_phase_inner := phaseTransport_inner
  quotient_composition := quotientPhase_add

end GeneratedFoundations.Arithmetic.HistoryChargedTransport
