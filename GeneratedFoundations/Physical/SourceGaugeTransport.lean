module

public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Physical.GlobalGaugeKernel

/-!
# The reduced gauge action on the source matter carrier

The six coordinate blocks are obtained by a specified rearrangement of
the orthonormal colour, retained-line, spin and chiral basis. The spin
basis is the image of the original Gaussian vacuum and first excitation.
Conjugating the complete block representation by this coordinate map
therefore defines an action on the actual source matter space. Its exact
kernel is transported by an explicit intertwining relation.

This construction uses the localized frame action and the vacuum
reduction of the specified realization rules. It does not infer those
rules from the unreduced source group alone.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGaugeTransport

open SourceChiralCarrier

/-- The six conventional blocks retain every one of the sixteen source coordinates. -/
def pack : (FullIndex → ℂ) →ₗ[ℂ] GlobalGaugeKernel.Matter where
  toFun f :=
    ((fun i => f (Sum.inl i.1, Sum.inl i.2), fun s => f (Sum.inr 0, Sum.inl s)),
      ((fun c => f (Sum.inl c, Sum.inr 0), fun c => f (Sum.inl c, Sum.inr 1)),
        (fun c => f (Sum.inr c, Sum.inr 0), fun c => f (Sum.inr c, Sum.inr 1))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unpack : GlobalGaugeKernel.Matter →ₗ[ℂ] (FullIndex → ℂ) where
  toFun x
    | (Sum.inl c, Sum.inl s) => x.1.1 (c, s)
    | (Sum.inr _, Sum.inl s) => x.1.2 s
    | (Sum.inl c, Sum.inr s) => if s = 0 then x.2.1.1 c else x.2.1.2 c
    | (Sum.inr c, Sum.inr s) => if s = 0 then x.2.2.1 c else x.2.2.2 c
  map_add' x y := by
    funext ⟨c, s⟩
    rcases c with c | c <;> rcases s with s | s <;> fin_cases s <;> rfl
  map_smul' a x := by
    funext ⟨c, s⟩
    rcases c with c | c <;> rcases s with s | s <;> fin_cases s <;> rfl

theorem unpack_pack (f : FullIndex → ℂ) : unpack (pack f) = f := by
  funext ⟨c, s⟩
  cases c with
  | inl c =>
      cases s with
      | inl s => rfl
      | inr s => fin_cases s <;> simp [unpack, pack]
  | inr c =>
      fin_cases c
      cases s with
      | inl s => rfl
      | inr s => fin_cases s <;> simp [unpack, pack]

theorem pack_unpack (x : GlobalGaugeKernel.Matter) : pack (unpack x) = x := by
  apply Prod.ext
  · apply Prod.ext <;> rfl
  · apply Prod.ext
    · apply Prod.ext <;> funext c <;> simp [pack, unpack]
    · apply Prod.ext <;> funext c <;> simp [pack, unpack]

def splitCoordinates : (FullIndex → ℂ) ≃ₗ[ℂ] GlobalGaugeKernel.Matter where
  toLinearMap := pack
  invFun := unpack
  left_inv := unpack_pack
  right_inv := pack_unpack

/-- Coordinates preserve the actual tensor labels before the block rearrangement. -/
def coordinates : FullMatter ≃ₗ[ℂ] GlobalGaugeKernel.Matter :=
  fullBasis.toBasis.equivFun.trans splitCoordinates

theorem orthonormalBasis_equivFun {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : OrthonormalBasis ι ℂ E) (i : ι) :
    e.toBasis.equivFun (e i) = Pi.single i 1 := by
  funext j
  simp [Pi.single_apply, eq_comm]

theorem coordinates_basis (i : FullIndex) :
    coordinates (fullBasis i) = pack (Pi.single i 1) :=
  congrArg pack (orthonormalBasis_equivFun fullBasis i)

def transportRepresentation {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) : G →* Module.End ℂ E :=
  (e.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp ρ

/-- The matrix-coordinate action acts on the original source Hilbert carrier
through a concrete coordinate equivalence. -/
def representation : GlobalGaugeKernel.GaugeGroup →* Module.End ℂ FullMatter :=
  transportRepresentation coordinates GlobalGaugeKernel.representation

theorem conjugate_intertwines {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (A : Module.End ℂ F) (x : E) :
    e ((e.symm.conjAlgEquiv ℂ) A x) = A (e x) :=
  e.apply_symm_apply _

theorem conjugate_eq_one_iff {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (A : Module.End ℂ F) :
    (e.symm.conjAlgEquiv ℂ) A = 1 ↔ A = 1 := by
  constructor
  · intro h
    exact (e.symm.conjAlgEquiv ℂ).injective (h.trans (map_one (e.symm.conjAlgEquiv ℂ)).symm)
  · rintro rfl
    exact map_one (e.symm.conjAlgEquiv ℂ)

theorem transportRepresentation_intertwines {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) (x : E) :
    e (transportRepresentation e ρ g x) = ρ g (e x) :=
  conjugate_intertwines e (ρ g) x

theorem transportRepresentation_eq_one_iff {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) :
    transportRepresentation e ρ g = 1 ↔ ρ g = 1 :=
  conjugate_eq_one_iff e (ρ g)

theorem transportRepresentation_intertwines_linear {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) :
    e.toLinearMap.comp (transportRepresentation e ρ g) = (ρ g).comp e.toLinearMap := by
  apply LinearMap.ext
  exact transportRepresentation_intertwines e ρ g

theorem coordinates_intertwines_linear (g : GlobalGaugeKernel.GaugeGroup) :
    coordinates.toLinearMap.comp (representation g) =
      (GlobalGaugeKernel.representation g).comp coordinates.toLinearMap :=
  transportRepresentation_intertwines_linear coordinates GlobalGaugeKernel.representation g

theorem coordinates_intertwines (g : GlobalGaugeKernel.GaugeGroup) (x : FullMatter) :
    coordinates (representation g x) = GlobalGaugeKernel.representation g (coordinates x) :=
  LinearMap.congr_fun (coordinates_intertwines_linear g) x

theorem representation_eq_one_iff (g : GlobalGaugeKernel.GaugeGroup) :
    representation g = 1 ↔ GlobalGaugeKernel.representation g = 1 :=
  transportRepresentation_eq_one_iff coordinates GlobalGaugeKernel.representation g

/-- The kernel is unchanged by the actual source-coordinate intertwiner. -/
theorem kernel_eq : representation.ker = GlobalGaugeKernel.representation.ker := by
  ext g
  exact representation_eq_one_iff g

theorem source_kernel_iff (g3 : GlobalGaugeKernel.SU3)
    (gL : Operations.SourceSpinCornerGroup.SU2) (z : Circle) :
    representation (g3, gL, z) = 1 ↔ z ^ 6 = 1 ∧
      (g3 : GlobalGaugeKernel.Mat3) = (z : ℂ) ^ 2 • (1 : GlobalGaugeKernel.Mat3) ∧
      (gL : Operations.SourceSpinCorner.Mat2) =
        (z : ℂ) ^ 3 • (1 : Operations.SourceSpinCorner.Mat2) := by
  rw [representation_eq_one_iff, GlobalGaugeKernel.representation_kernel_iff]

theorem kernel_eq_zpowers :
    representation.ker = Subgroup.zpowers GlobalGaugeKernel.generator := by
  rw [kernel_eq, GlobalGaugeKernel.kernel_eq_zpowers]

theorem kernel_card : Nat.card representation.ker = 6 := by
  rw [kernel_eq, GlobalGaugeKernel.kernel_card]

theorem kernel_iff_generator_power (g : GlobalGaugeKernel.GaugeGroup) :
    representation g = 1 ↔ ∃ n : ℕ, n < 6 ∧ GlobalGaugeKernel.generator ^ n = g := by
  rw [representation_eq_one_iff, GlobalGaugeKernel.kernel_iff_generator_power]

/-- The residual phase acts on the complete matter carrier with fixed
colour and weak frames. Its faithfulness is proved below. -/
def phaseAction : Circle →* Module.End ℂ FullMatter where
  toFun z := representation (1, 1, z)
  map_one' := representation.map_one
  map_mul' z w := by
    simpa using representation.map_mul (1, 1, z) (1, 1, w)

theorem phaseAction_eq_one_iff (z : Circle) : phaseAction z = 1 ↔ z = 1 := by
  change representation (1, 1, z) = 1 ↔ _
  constructor
  · intro h
    obtain ⟨_, hc, hw⟩ := (source_kernel_iff 1 1 z).mp h
    have htwo : (z : ℂ) ^ 2 = 1 := by
      simpa using (congrArg (fun M : GlobalGaugeKernel.Mat3 => M 0 0) hc).symm
    have hthree : (z : ℂ) ^ 3 = 1 := by
      simpa using (congrArg (fun M : Operations.SourceSpinCorner.Mat2 => M 0 0) hw).symm
    have hz : (z : ℂ) = 1 := by
      rw [pow_succ, htwo, one_mul] at hthree
      exact hthree
    exact Circle.coe_eq_one.mp hz
  · rintro rfl
    exact representation.map_one

theorem phaseAction_injective : Function.Injective phaseAction := by
  intro z w h
  apply mul_inv_eq_one.mp
  apply (phaseAction_eq_one_iff (z * w⁻¹)).mp
  calc
    phaseAction (z * w⁻¹) = phaseAction z * phaseAction w⁻¹ := phaseAction.map_mul z w⁻¹
    _ = phaseAction w * phaseAction w⁻¹ := congrArg (fun A => A * phaseAction w⁻¹) h
    _ = phaseAction (w * w⁻¹) := (phaseAction.map_mul w w⁻¹).symm
    _ = phaseAction 1 := congrArg phaseAction (mul_inv_cancel w)
    _ = 1 := phaseAction.map_one

def phaseFlow (t : ℝ) : Module.End ℂ FullMatter := phaseAction (SourcePhaseLift.phase t)

@[simp] theorem phaseFlow_zero : phaseFlow 0 = 1 := by
  simp [phaseFlow]

theorem phaseFlow_add (s t : ℝ) : phaseFlow (s + t) = phaseFlow s * phaseFlow t := by
  simp only [phaseFlow, SourcePhaseLift.phase, add_div, Circle.exp_add, map_mul]

theorem phaseFlow_eq_one_iff (t : ℝ) :
    phaseFlow t = 1 ↔ ∃ k : ℤ, t = k * (12 * Real.pi) := by
  rw [phaseFlow, phaseAction_eq_one_iff, SourcePhaseLift.phase, Circle.exp_eq_one]
  constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩ <;> linarith

theorem phaseFlow_periodic_iff (t : ℝ) :
    Function.Periodic phaseFlow t ↔ ∃ k : ℤ, t = k * (12 * Real.pi) := by
  constructor
  · intro h
    apply (phaseFlow_eq_one_iff t).mp
    simpa using h 0
  · rintro ⟨k, rfl⟩ s
    have hp : SourcePhaseLift.phase (s + k * (12 * Real.pi)) = SourcePhaseLift.phase s := by
      unfold SourcePhaseLift.phase
      rw [show (s + k * (12 * Real.pi)) / 6 = s / 6 + k * (2 * Real.pi) by ring,
        Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    simp only [phaseFlow, hp]

/-- The twelve-pi period is detected by the full matter action, not inferred
from a period of its two-dimensional scalar restriction. -/
theorem phaseFlow_least_positive_period :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic phaseFlow t} (12 * Real.pi) := by
  have he : {t : ℝ | 0 < t ∧ Function.Periodic phaseFlow t} =
      {t : ℝ | 0 < t ∧ Function.Periodic SourcePhaseLift.lift t} := by
    ext t
    simp only [Set.mem_ofPred_eq, phaseFlow_periodic_iff, SourcePhaseLift.lift_periodic_iff]
  rw [he]
  exact SourcePhaseLift.lift_least_positive_period

/-- In the generated sixteen-state Hermite corner, the same reduced action
has the full-source matrix, not a separately chosen collection of weights. -/
theorem hermite_action {b : ℝ} (hb : 0 < b) (g : GlobalGaugeKernel.GaugeGroup)
    (x : FullMatter) :
    hermiteIsometry hb (representation g x) =
      Operations.FiniteHermiteCorner.corner hb
        (SourceCliffordConnector.sourceMode (d := 4))
        (fullMatrixCoordinates (representation g)) (hermiteIsometry hb x) :=
  hermiteIsometry_intertwines hb (representation g) x

end GeneratedFoundations.Physical.SourceGaugeTransport
