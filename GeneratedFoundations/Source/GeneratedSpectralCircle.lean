module

public import GeneratedFoundations.Source.CarrierOrientation
public import GeneratedFoundations.Source.OriginalLieFlow
public import GeneratedFoundations.Arithmetic.NativeModes

/-!
# The generated carrier and the reflecting spectral circle

The orientation of the original real carrier selects a trace-unit vector in
the original Lie algebra. Its previously constructed integral curve determines
a unique continuous phase character. Rescaling the covering coordinate then
identifies this same group with the circle of circumference twice the retained
interval length. The group, its atlas, and its integral curve are unchanged.

The resulting comparison is a continuous group isomorphism. No smoothness of
its inverse in the original atlas is asserted. Fourier characters on the
spectral circle are identified with the existing actual circle power maps;
the identification of positive Fourier modes with an intrinsic positive
spectral channel of a first-order operator is a separate analytic statement.
-/

@[expose] public section

noncomputable section

open Function
open scoped Topology Manifold

namespace GeneratedFoundations.Source.GeneratedSpectralCircle

open CarrierOrientation OriginalLieFlow TraceLieGeometry
open GeneratedFoundations.Arithmetic

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

/-- The parameterized subgroup is the original left-invariant integral curve. -/
def orientedFlow (o : OrientationOnCarrier d) : ℝ → d.Changes :=
  flow d (carrierUnit d h o).tangent

@[simp]
theorem orientedFlow_zero (o : OrientationOnCarrier d) : orientedFlow d h o 0 = 1 :=
  flow_zero d _

theorem orientedFlow_add (o : OrientationOnCarrier d) (s t : ℝ) :
    orientedFlow d h o (s + t) = orientedFlow d h o s * orientedFlow d h o t :=
  flow_add d _ s t

theorem orientedFlow_continuous (o : OrientationOnCarrier d) :
    Continuous (orientedFlow d h o) := flow_continuous d _

theorem orientedFlow_reverse (o : OrientationOnCarrier d) (t : ℝ) :
    orientedFlow d h (-o) t = orientedFlow d h o (-t) := by
  simp only [orientedFlow, carrierUnit_reverse]
  change flow d (-(carrierUnit d h o).tangent) t =
    flow d (carrierUnit d h o).tangent (-t)
  simpa only [neg_one_smul, mul_neg_one] using
    flow_smul d (carrierUnit d h o).tangent (-1) t

def circleInversion : Circle ≃ₜ* Circle where
  toFun z := z⁻¹
  invFun z := z⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' z w := by simp [mul_comm]
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

theorem coordinate_phase_flow (e : d.Carrier ≃ₗᵢ[ℝ] ℂ)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (t : ℝ) :
    χ (orientedFlow d h (coordinateOrientation d e) t) = Circle.exp t := by
  apply Subtype.ext
  change (χ (flow d (carrierUnit d h (coordinateOrientation d e)).tangent t) : ℂ) =
    Complex.exp ((t : ℂ) * Complex.I)
  rw [carrierUnit_coordinate d h e χ hχ haction]
  change (χ.toMonoidHom (flow d (positiveUnit d h χ hχ).tangent t) : ℂ) =
    Complex.exp ((t : ℂ) * Complex.I)
  simpa only [positiveUnit_differential] using
    character_flow d χ.toMonoidHom hχ (positiveUnit d h χ hχ).tangent t

/-- Existence is obtained from the original representation classification and
the actual integral-curve equation, with the sign fixed by the carrier. -/
theorem phaseCharacter_exists (o : OrientationOnCarrier d) :
    ∃ χ : d.Changes ≃ₜ* Circle, ∀ t, χ (orientedFlow d h o t) = Circle.exp t := by
  obtain ⟨_, e, χ, hχ, hχinv, haction⟩ :=
    MinimalCarrier.minimalCarrier_classification d h
  let c : d.Changes ≃ₜ* Circle :=
    { χ with continuous_toFun := hχ, continuous_invFun := hχinv }
  rcases carrier_orientation_cases d h o (coordinateOrientation d e) with ho | ho
  · refine ⟨c, ?_⟩
    intro t
    rw [ho]
    exact coordinate_phase_flow d h e χ hχ haction t
  · refine ⟨c.trans circleInversion, ?_⟩
    intro t
    change (χ (orientedFlow d h o t))⁻¹ = Circle.exp t
    rw [ho, orientedFlow_reverse, coordinate_phase_flow d h e χ hχ haction]
    simp only [Circle.exp_neg, inv_inv]

def phaseCharacter (o : OrientationOnCarrier d) : d.Changes ≃ₜ* Circle :=
  Classical.choose (phaseCharacter_exists d h o)

theorem phaseCharacter_flow (o : OrientationOnCarrier d) (t : ℝ) :
    phaseCharacter d h o (orientedFlow d h o t) = Circle.exp t :=
  Classical.choose_spec (phaseCharacter_exists d h o) t

theorem orientedFlow_surjective (o : OrientationOnCarrier d) :
    Function.Surjective (orientedFlow d h o) := by
  intro g
  obtain ⟨t, ht⟩ := Circle.exp_surjective (phaseCharacter d h o g)
  refine ⟨t, (phaseCharacter d h o).injective ?_⟩
  exact (phaseCharacter_flow d h o t).trans ht

/-- The phase coordinate is independent of the auxiliary classification
coordinate, since the original oriented flow reaches every group element. -/
theorem phaseCharacter_unique (o : OrientationOnCarrier d)
    (χ : d.Changes ≃ₜ* Circle)
    (hχ : ∀ t, χ (orientedFlow d h o t) = Circle.exp t) :
    χ = phaseCharacter d h o := by
  apply ContinuousMulEquiv.ext
  intro g
  obtain ⟨t, rfl⟩ := orientedFlow_surjective d h o g
  exact (hχ t).trans (phaseCharacter_flow d h o t).symm

theorem phaseCharacter_existsUnique (o : OrientationOnCarrier d) :
    ∃! χ : d.Changes ≃ₜ* Circle,
      ∀ t, χ (orientedFlow d h o t) = Circle.exp t :=
  ⟨phaseCharacter d h o, phaseCharacter_flow d h o,
    fun χ hχ => phaseCharacter_unique d h o χ hχ⟩

theorem orientedFlow_eq_inverse_phase (o : OrientationOnCarrier d) (t : ℝ) :
    orientedFlow d h o t = (phaseCharacter d h o).symm (Circle.exp t) := by
  apply (phaseCharacter d h o).injective
  rw [phaseCharacter_flow, ContinuousMulEquiv.apply_symm_apply]

/-- The covering property is transported only after the original flow has
been constructed and its scalar phase has been proved. -/
theorem orientedFlow_isQuotientCoveringMap (o : OrientationOnCarrier d) :
    IsAddQuotientCoveringMap (orientedFlow d h o)
      (AddSubgroup.zmultiples (2 * Real.pi)) := by
  have hc := Circle.isAddQuotientCoveringMap_exp.homeomorph_comp
    (phaseCharacter d h o).toHomeomorph.symm
  convert hc using 1
  funext t
  exact orientedFlow_eq_inverse_phase d h o t

theorem orientedFlow_eq_iff (o : OrientationOnCarrier d) (s t : ℝ) :
    orientedFlow d h o s = orientedFlow d h o t ↔
      ∃ k : ℤ, s = t + k * (2 * Real.pi) := by
  rw [← (phaseCharacter d h o).injective.eq_iff,
    phaseCharacter_flow, phaseCharacter_flow, Circle.exp_eq_exp]

theorem orientedFlow_kernel (o : OrientationOnCarrier d) (t : ℝ) :
    orientedFlow d h o t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← (phaseCharacter d h o).injective.eq_iff, phaseCharacter_flow,
    map_one, Circle.exp_eq_one]

theorem orientedFlow_periodic (o : OrientationOnCarrier d) :
    Function.Periodic (orientedFlow d h o) (2 * Real.pi) := by
  intro t
  exact (orientedFlow_eq_iff d h o _ _).mpr ⟨1, by simp⟩

theorem orientedFlow_least_positive_period (o : OrientationOnCarrier d)
    (p : ℝ) (hp : 0 < p) (hperiod : Function.Periodic (orientedFlow d h o) p) :
    2 * Real.pi ≤ p := by
  have hzero : orientedFlow d h o p = 1 := by
    simpa only [zero_add, orientedFlow_zero] using hperiod 0
  obtain ⟨k, hk⟩ := (orientedFlow_kernel d h o p).mp hzero
  have hkpos : (0 : ℝ) < k := by nlinarith [Real.pi_pos]
  have hkint : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkint
  nlinarith [Real.pi_pos]

theorem phaseCharacter_reverse (o : OrientationOnCarrier d) (g : d.Changes) :
    phaseCharacter d h (-o) g = (phaseCharacter d h o g)⁻¹ := by
  obtain ⟨t, rfl⟩ := orientedFlow_surjective d h (-o) g
  rw [phaseCharacter_flow, orientedFlow_reverse, phaseCharacter_flow,
    Circle.exp_neg, inv_inv]

variable (L : ℝ) [hL : Fact (0 < L)]

/-- The standard phase of the actual reflecting circle of circumference `2L`. -/
def spectralPhase : Multiplicative (AddCircle (2 * L)) ≃ₜ* Circle where
  toFun x := AddCircle.toCircle x.toAdd
  invFun z := Multiplicative.ofAdd
    ((AddCircle.homeomorphCircle (T := 2 * L) (mul_ne_zero two_ne_zero hL.out.ne')).symm z)
  left_inv x := by
    change Multiplicative.ofAdd
      ((AddCircle.homeomorphCircle (T := 2 * L) (mul_ne_zero two_ne_zero hL.out.ne')).symm
        (AddCircle.toCircle x.toAdd)) = x
    rw [← AddCircle.homeomorphCircle_apply (mul_ne_zero two_ne_zero hL.out.ne'),
      Homeomorph.symm_apply_apply]
    rfl
  right_inv z := by
    change AddCircle.toCircle
      ((AddCircle.homeomorphCircle (T := 2 * L) (mul_ne_zero two_ne_zero hL.out.ne')).symm z) = z
    rw [← AddCircle.homeomorphCircle_apply (mul_ne_zero two_ne_zero hL.out.ne'),
      Homeomorph.apply_symm_apply]
  map_mul' x y := AddCircle.toCircle_add x.toAdd y.toAdd
  continuous_toFun := AddCircle.continuous_toCircle.comp continuous_toAdd
  continuous_invFun := continuous_ofAdd.comp
    (AddCircle.homeomorphCircle (T := 2 * L) (mul_ne_zero two_ne_zero hL.out.ne')).symm.continuous

@[simp]
theorem spectralPhase_apply (x : AddCircle (2 * L)) :
    spectralPhase L (Multiplicative.ofAdd x) = AddCircle.toCircle x := rfl

/-- A continuous group isomorphism from the original group to the reflecting
circle. Multiplicative notation here only tags the additive quotient group. -/
def carrierCircle (o : OrientationOnCarrier d) :
    d.Changes ≃ₜ* Multiplicative (AddCircle (2 * L)) :=
  (phaseCharacter d h o).trans (spectralPhase L).symm

def spectralCoordinate (o : OrientationOnCarrier d) (g : d.Changes) :
    AddCircle (2 * L) := (carrierCircle d h L o g).toAdd

theorem spectralCoordinate_continuous (o : OrientationOnCarrier d) :
    Continuous (spectralCoordinate d h L o) :=
  continuous_toAdd.comp (carrierCircle d h L o).continuous

theorem spectralCoordinate_mul (o : OrientationOnCarrier d) (g k : d.Changes) :
    spectralCoordinate d h L o (g * k) =
      spectralCoordinate d h L o g + spectralCoordinate d h L o k :=
  congrArg Multiplicative.toAdd ((carrierCircle d h L o).map_mul g k)

theorem spectralCoordinate_phase (o : OrientationOnCarrier d) (g : d.Changes) :
    AddCircle.toCircle (spectralCoordinate d h L o g) = phaseCharacter d h o g :=
  (spectralPhase L).apply_symm_apply _

theorem covering_coordinate_phase (t : ℝ) :
    AddCircle.toCircle ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) = Circle.exp t := by
  rw [AddCircle.toCircle_apply_mk]
  congr 1
  field_simp [hL.out.ne', Real.pi_ne_zero]

/-- The scale factor is forced by the common phase of the original flow and
the reflecting circle; it is not an input to the character construction. -/
theorem spectralCoordinate_flow (o : OrientationOnCarrier d) (t : ℝ) :
    spectralCoordinate d h L o (orientedFlow d h o t) =
      ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) := by
  apply AddCircle.injective_toCircle (mul_ne_zero two_ne_zero hL.out.ne')
  rw [spectralCoordinate_phase, phaseCharacter_flow, covering_coordinate_phase]

theorem carrierCircle_unique (o : OrientationOnCarrier d)
    (C : d.Changes ≃ₜ* Multiplicative (AddCircle (2 * L)))
    (hC : ∀ t, (C (orientedFlow d h o t)).toAdd =
      ((L / Real.pi * t : ℝ) : AddCircle (2 * L))) :
    C = carrierCircle d h L o := by
  ext g
  obtain ⟨t, rfl⟩ := orientedFlow_surjective d h o g
  exact congrArg Multiplicative.ofAdd
    ((hC t).trans (spectralCoordinate_flow d h L o t).symm)

theorem carrierCircle_existsUnique (o : OrientationOnCarrier d) :
    ∃! C : d.Changes ≃ₜ* Multiplicative (AddCircle (2 * L)),
      ∀ t, (C (orientedFlow d h o t)).toAdd =
        ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) :=
  ⟨carrierCircle d h L o, spectralCoordinate_flow d h L o,
    fun C hC => carrierCircle_unique d h L o C hC⟩

omit hL in
theorem reflecting_cover_kernel (x : ℝ) :
    (x : AddCircle (2 * L)) = 0 ↔ ∃ k : ℤ, x = k * (2 * L) := by
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [zsmul_eq_mul] using hk.symm⟩

theorem covering_kernel_correspondence (t : ℝ) :
    ((L / Real.pi * t : ℝ) : AddCircle (2 * L)) = 0 ↔
      ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← (AddCircle.injective_toCircle (mul_ne_zero two_ne_zero hL.out.ne')).eq_iff,
    covering_coordinate_phase, AddCircle.toCircle_zero, Circle.exp_eq_one]

theorem spectralCoordinate_reverse (o : OrientationOnCarrier d) (g : d.Changes) :
    spectralCoordinate d h L (-o) g = -spectralCoordinate d h L o g := by
  apply AddCircle.injective_toCircle (mul_ne_zero two_ne_zero hL.out.ne')
  rw [spectralCoordinate_phase, AddCircle.toCircle_neg, spectralCoordinate_phase,
    phaseCharacter_reverse]

theorem spectral_fourier_phase (o : OrientationOnCarrier d) (n : ℤ) (g : d.Changes) :
    fourier n (spectralCoordinate d h L o g) = (phaseCharacter d h o g : ℂ) ^ n := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, spectralCoordinate_phase, Circle.coe_zpow]

theorem spectral_fourier_flow (o : OrientationOnCarrier d) (n : ℤ) (t : ℝ) :
    fourier n (spectralCoordinate d h L o (orientedFlow d h o t)) =
      (Circle.exp t : ℂ) ^ n := by
  rw [spectral_fourier_phase, phaseCharacter_flow]

theorem spectral_fourier_nativeMode (o : OrientationOnCarrier d) (n : ℕ) (g : d.Changes) :
    fourier (n : ℤ) (spectralCoordinate d h L o g) =
      (NativeModes.powerMode n (phaseCharacter d h o g) : ℂ) := by
  rw [spectral_fourier_phase, NativeModes.powerMode_apply, Circle.coe_pow]
  simp only [zpow_natCast]

/-- Both source and target are transported when a circle endomorphism is
viewed on the original carrier. This preserves actual map composition. -/
def transportEndomorphism (o : OrientationOnCarrier d) (u : Circle →ₜ* Circle) :
    d.Changes →ₜ* d.Changes where
  toFun g := (phaseCharacter d h o).symm (u (phaseCharacter d h o g))
  map_one' := by simp
  map_mul' g k := by simp
  continuous_toFun := (phaseCharacter d h o).symm.continuous.comp
    (u.continuous.comp (phaseCharacter d h o).continuous)

theorem transportEndomorphism_comp (o : OrientationOnCarrier d)
    (u v : Circle →ₜ* Circle) :
    transportEndomorphism d h o (u.comp v) =
      (transportEndomorphism d h o u).comp (transportEndomorphism d h o v) := by
  apply DFunLike.ext
  intro g
  change (phaseCharacter d h o).symm (u (v (phaseCharacter d h o g))) =
    (phaseCharacter d h o).symm
      (u (phaseCharacter d h o ((phaseCharacter d h o).symm (v (phaseCharacter d h o g)))))
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem transportEndomorphism_power (o : OrientationOnCarrier d) (n : ℤ) (g : d.Changes) :
    transportEndomorphism d h o (CircleEndomorphisms.powerEndomorphism n) g = g ^ n := by
  change (phaseCharacter d h o).symm ((phaseCharacter d h o g) ^ n) = g ^ n
  rw [map_zpow, ContinuousMulEquiv.symm_apply_apply]

end GeneratedFoundations.Source.GeneratedSpectralCircle
