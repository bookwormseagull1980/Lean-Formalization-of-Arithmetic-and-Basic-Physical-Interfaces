module

public import GeneratedFoundations.Source.ClosedCircleSubgroups
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Ring

/-!
# Compact connected orthogonal actions on a real plane

Connectedness rules out orientation-reversing isometries. A faithful compact
connected action then has the full circle as its image. The coordinate
isometry is chosen only after the real dimension has been specified.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Source.ConnectedPlaneAction

variable {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]

theorem orientation_ratio_mem_pair (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    f Complex.I / f 1 ∈ ({Complex.I, -Complex.I} : Set ℂ) := by
  obtain ⟨z, h | h⟩ := linear_isometry_complex f
  · left
    simp only [h, rotation_apply, mul_one]
    exact (div_eq_iff z.coe_ne_zero).mpr (mul_comm _ _)
  · right
    simp only [Set.mem_singleton_iff, h, LinearIsometryEquiv.trans_apply,
      Complex.conjLIE_apply, rotation_apply, map_one, mul_one, Complex.conj_I]
    exact (div_eq_iff z.coe_ne_zero).mpr (mul_comm _ _)

theorem action_is_rotation (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w)) (g : G) :
    ∃ z : Circle, ρ g = rotation z := by
  let ε : G → ℂ := fun k => ρ k Complex.I / ρ k 1
  have hnz (k : G) : ρ k 1 ≠ 0 := by
    simp
  have hc : Continuous ε := (hcontinuous Complex.I).div (hcontinuous 1) hnz
  have hm : Set.MapsTo ε Set.univ ({Complex.I, -Complex.I} : Set ℂ) :=
    fun k _ => orientation_ratio_mem_pair (ρ k)
  have he := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({Complex.I, -Complex.I} : Set ℂ)).isDiscrete hc.continuousOn hm
    (Set.mem_univ g) (Set.mem_univ (1 : G))
  have he' : ρ g Complex.I / ρ g 1 = Complex.I := by simpa [ε] using he
  obtain ⟨z, h | h⟩ := linear_isometry_complex (ρ g)
  · exact ⟨z, h⟩
  · have hneg : ρ g Complex.I / ρ g 1 = -Complex.I := by
      simp only [h, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply,
        rotation_apply, map_one, mul_one, Complex.conj_I]
      exact (div_eq_iff z.coe_ne_zero).mpr (mul_comm _ _)
    have him := congrArg Complex.im (he'.symm.trans hneg)
    norm_num at him

def character (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w)) : G →* Circle where
  toFun g := ⟨ρ g 1, by
    simp [Submonoid.unitSphere]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := action_is_rotation ρ hcontinuous g
    change (ρ (g * h)) 1 = (ρ g) 1 * (ρ h) 1
    rw [map_mul]
    change ρ g (ρ h 1) = _
    simp [hz]

@[simp] theorem character_apply (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w)) (g : G) :
    (character ρ hcontinuous g : ℂ) = ρ g 1 := rfl

theorem action_eq_character_mul (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w)) (g : G) (w : ℂ) :
    ρ g w = (character ρ hcontinuous g : ℂ) * w := by
  obtain ⟨z, hz⟩ := action_is_rotation ρ hcontinuous g
  simp [hz]

theorem character_continuous (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w)) :
    Continuous (character ρ hcontinuous) := (hcontinuous 1).subtype_mk _

theorem character_faithful (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w))
    (hfaithful : Function.Injective ρ) : Function.Injective (character ρ hcontinuous) := by
  intro g h hgh
  apply hfaithful
  apply LinearIsometryEquiv.ext
  intro w
  rw [action_eq_character_mul ρ hcontinuous, action_eq_character_mul ρ hcontinuous, hgh]

theorem character_surjective [CompactSpace G] [Nontrivial G]
    (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w))
    (hfaithful : Function.Injective ρ) : Function.Surjective (character ρ hcontinuous) :=
  ClosedCircleSubgroups.surjective_of_compact_connected (character ρ hcontinuous)
    (character_continuous ρ hcontinuous) (character_faithful ρ hcontinuous hfaithful)

def circleEquiv [CompactSpace G] [Nontrivial G]
    (ρ : G →* (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hcontinuous : ∀ w : ℂ, Continuous (fun g : G => ρ g w))
    (hfaithful : Function.Injective ρ) : G ≃* Circle :=
  MulEquiv.ofBijective (character ρ hcontinuous)
    ⟨character_faithful ρ hcontinuous hfaithful,
      character_surjective ρ hcontinuous hfaithful⟩

def planeCoordinate {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2) : V ≃ₗᵢ[ℝ] ℂ :=
  (stdOrthonormalBasis ℝ V).equiv Complex.orthonormalBasisOneI (finCongr hdim)

def conjugateAction {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : V ≃ₗᵢ[ℝ] ℂ) (ρ : G →* (V ≃ₗᵢ[ℝ] V)) : G →* (ℂ ≃ₗᵢ[ℝ] ℂ) where
  toFun g := (e.symm.trans (ρ g)).trans e
  map_one' := by apply LinearIsometryEquiv.ext; intro z; simp
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro z
    change e (ρ (g * h) (e.symm z)) = e (ρ g (e.symm (e (ρ h (e.symm z)))))
    simp

theorem plane_action_classification {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [CompactSpace G] [Nontrivial G]
    (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hcontinuous : ∀ v : V, Continuous (fun g : G => ρ g v))
    (hfaithful : Function.Injective ρ) (hdim : Module.finrank ℝ V = 2) :
    ∃ (e : V ≃ₗᵢ[ℝ] ℂ) (f : G ≃* Circle),
      Continuous f ∧ Continuous f.symm ∧
        ∀ g v, e (ρ g v) = (f g : ℂ) * e v := by
  let e := planeCoordinate hdim
  let σ := conjugateAction e ρ
  have hc (w : ℂ) : Continuous (fun g : G => σ g w) :=
    e.continuous.comp (hcontinuous (e.symm w))
  have hf : Function.Injective σ := by
    intro g h hgh
    apply hfaithful
    apply LinearIsometryEquiv.ext
    intro v
    have hv := LinearIsometryEquiv.congr_fun hgh (e v)
    have heq : e (ρ g v) = e (ρ h v) := by
      simpa [σ, conjugateAction] using hv
    exact e.injective heq
  let f := circleEquiv σ hc hf
  have hfc : Continuous f := character_continuous σ hc
  refine ⟨e, f, hfc, ?_, ?_⟩
  · exact hfc.continuous_symm_of_equiv_compact_to_t2
  · intro g v
    have h := action_eq_character_mul σ hc g (e v)
    simpa [σ, conjugateAction, f, circleEquiv] using h

end GeneratedFoundations.Source.ConnectedPlaneAction
