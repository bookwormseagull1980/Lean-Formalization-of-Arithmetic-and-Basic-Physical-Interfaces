module

public import GeneratedFoundations.Arithmetic.HistoryGeneratedFrameGroup
public import GeneratedFoundations.Arithmetic.HistoryJointCircleAction

/-!
# Joint source frames and relative phase on complete arithmetic prefixes

The carrier contains every root below the prefix, every history, every phase,
and all four source coordinates. The coordinates below are a unitary
rearrangement of the existing Clifford carrier. Source frames and the
rank-derived relative phase act on this same carrier and commute.

Their joint kernel is computed using occupied fibres. The root-one fibre
fixes the source frame; the root-two detail space detects the primitive
circle character. Thus a prefix containing both roots has a faithful joint
action. The response kernel is not copied from the physical charged carrier.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCompleteSourceGroup

open HistoryJointChargeLattice (Spin)
open HistoryRootSectors (Roots)
open Geometry.SourceScalarResponse (Frame)

abbrev Space (N : ℕ) := PiLp 2 fun b : Roots N => HistoryJointCharge.Space b.val
abbrev Presentation := Frame × Circle
abbrev PhaseGroup := Circle

def indexCoordinates (N : ℕ) : HistoryCliffordAction.Index N ≃
    (Σ b : Roots N, Σ _ : Spin, HistoryModuleRepresentation.Index b.val) where
  toFun p := ⟨p.1.1, ⟨p.2, p.1.2⟩⟩
  invFun p := ⟨⟨p.1, p.2.2⟩, p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete unitary coordinates, including off-diagonal root responses. -/
def coordinates (N : ℕ) : HistoryCliffordAction.Space N ≃ₗᵢ[ℂ] Space N :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (indexCoordinates N)).trans
    ((LinearIsometryEquiv.piLpCurry ℂ 2
      (fun (b : Roots N) (_ : Σ _ : Spin, HistoryModuleRepresentation.Index b.val) => ℂ)).trans
      (LinearIsometryEquiv.piLpCongrRight 2 fun b =>
        LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Spin)
          (_ : HistoryModuleRepresentation.Index b.val) => ℂ)))

@[simp] theorem coordinates_apply (N : ℕ) (x : HistoryCliffordAction.Space N)
    (b : Roots N) (s : Spin) (i : HistoryModuleRepresentation.Index b.val) :
    coordinates N x b s i = x (⟨b, i⟩, s) := rfl

@[simp] theorem coordinates_symm_apply (N : ℕ) (x : Space N)
    (b : Roots N) (s : Spin) (i : HistoryModuleRepresentation.Index b.val) :
    (coordinates N).symm x (⟨b, i⟩, s) = x b s i := rfl

theorem coordinates_inner (N : ℕ) (x y : HistoryCliffordAction.Space N) :
    inner ℂ (coordinates N x) (coordinates N y) = inner ℂ x y :=
  (coordinates N).inner_map_map x y

theorem coordinates_roundtrip (N : ℕ) (x : HistoryCliffordAction.Space N) :
    (coordinates N).symm (coordinates N x) = x :=
  (coordinates N).symm_apply_apply x

theorem coordinates_symm_roundtrip (N : ℕ) (x : Space N) :
    coordinates N ((coordinates N).symm x) = x :=
  (coordinates N).apply_symm_apply x

def source (N : ℕ) : Frame →* Module.End ℂ (Space N) :=
  Operations.UnitaryRepresentation.transportRepresentation
    (coordinates N).symm.toLinearEquiv (HistoryEffectiveFrames.stateResponse N)

def sourceMatrix (g : Frame) : Operations.SourceCliffordConnector.ChiralMatrix :=
  Operations.SourceCliffordComplex.complexPairMap
    ((g.1 : Operations.SourceSpinCorner.Mat2), (g.2 : Operations.SourceSpinCorner.Mat2))

theorem source_apply (N : ℕ) (g : Frame) (x : Space N)
    (b : Roots N) (s : Spin) :
    source N g x b s = ∑ t : Spin, sourceMatrix g s t • x b t := by
  apply PiLp.ext
  intro i
  cases s with
  | inl j =>
      change HistoryCliffordAction.action N (HistoryEvenResponse.matrix N
        ((g.1 : Operations.SourceSpinCorner.Mat2), (g.2 : Operations.SourceSpinCorner.Mat2)))
        ((coordinates N).symm x) (⟨b, i⟩, .inl j) = _
      rw [HistoryEvenResponse.matrix_left]
      simp [sourceMatrix, Operations.SourceCliffordComplex.complexPairMap,
        Fintype.sum_sum_type]
  | inr j =>
      change HistoryCliffordAction.action N (HistoryEvenResponse.matrix N
        ((g.1 : Operations.SourceSpinCorner.Mat2), (g.2 : Operations.SourceSpinCorner.Mat2)))
        ((coordinates N).symm x) (⟨b, i⟩, .inr j) = _
      rw [HistoryEvenResponse.matrix_right]
      simp [sourceMatrix, Operations.SourceCliffordComplex.complexPairMap,
        Fintype.sum_sum_type]

theorem source_inner (N : ℕ) (g : Frame) (x y : Space N) :
    inner ℂ (source N g x) (source N g y) = inner ℂ x y := by
  change inner ℂ (coordinates N (HistoryEffectiveFrames.stateResponse N g
    ((coordinates N).symm x))) (coordinates N (HistoryEffectiveFrames.stateResponse N g
    ((coordinates N).symm y))) = _
  rw [(coordinates N).inner_map_map, HistoryEffectiveFrames.stateResponse_inner]
  exact (coordinates N).symm.inner_map_map x y

def relative (N : ℕ) : Circle →* Module.End ℂ (Space N) where
  toFun z :=
    { toFun x := WithLp.toLp 2 fun b => HistoryJointCircleAction.action b.val 0 1 z (x b)
      map_add' x y := by ext b s i; simp
      map_smul' c x := by ext b s i; simp }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro b
    exact LinearMap.congr_fun (HistoryJointCircleAction.action_one b.val 0 1) (x b)
  map_mul' z w := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro b
    exact LinearMap.congr_fun (HistoryJointCircleAction.action_mul b.val 0 1 z w) (x b)

@[simp] theorem relative_apply (N : ℕ) (z : Circle) (x : Space N) (b : Roots N) :
    relative N z x b = HistoryJointCircleAction.action b.val 0 1 z (x b) := rfl

def phaseBlock (n : ℕ) (z : Circle) : Module.End ℂ (HistoryModuleRepresentation.Space n) :=
  HistoryRelativePhase.block n ((z : ℂ) ^ (-(n : ℤ)), (z : ℂ))

theorem relative_component (N : ℕ) (z : Circle) (x : Space N) (b : Roots N) (s : Spin) :
    relative N z x b s = phaseBlock b.val z (x b s) := by
  simp [HistoryJointCircleAction.action_apply, HistoryJointChargeLattice.weight,
    HistoryJointChargeLattice.relativeWeight, phaseBlock]

theorem relative_inner (N : ℕ) (z : Circle) (x y : Space N) :
    inner ℂ (relative N z x) (relative N z y) = inner ℂ x y := by
  simp only [PiLp.inner_apply, relative_apply]
  apply Finset.sum_congr rfl
  intro b _
  exact HistoryJointCircleAction.action_inner b.val 0 1 z (x b) (y b)

theorem source_relative_commute (N : ℕ) (g : Frame) (z : Circle) :
    source N g * relative N z = relative N z * source N g := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro b
  apply PiLp.ext
  intro s
  rw [Module.End.mul_apply, Module.End.mul_apply, source_apply, relative_component]
  rw [source_apply, map_sum]
  simp only [relative_component, map_smul]

def representation (N : ℕ) : Presentation →* Module.End ℂ (Space N) where
  toFun g := source N g.1 * relative N g.2
  map_one' := by simp
  map_mul' g h := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc
      _ = source N g.1 * (source N h.1 * relative N g.2) * relative N h.2 := by
        simp only [mul_assoc]
      _ = source N g.1 * (relative N g.2 * source N h.1) * relative N h.2 := by
        rw [source_relative_commute]
      _ = _ := by simp only [mul_assoc]

theorem representation_inner (N : ℕ) (g : Presentation) (x y : Space N) :
    inner ℂ (representation N g x) (representation N g y) = inner ℂ x y := by
  change inner ℂ (source N g.1 (relative N g.2 x))
    (source N g.1 (relative N g.2 y)) = _
  rw [source_inner, relative_inner]

/-- The root-one fibre already fixes both source matrices. -/
theorem joint_kernel_source (N : ℕ) (g : Presentation)
    (hg : representation N g = 1) : g.1 = 1 := by
  let b : Roots N := ⟨0, Nat.zero_lt_succ N⟩
  have hrelative (x : Space N) (s : Spin) : relative N g.2 x b s = x b s := by
    rw [relative_component]
    simp [phaseBlock, b, HistoryRelativePhase.block,
      HistoryRelativePhaseKernel.projection_zero, HistoryRelativePhaseKernel.residual_zero]
  have hM : sourceMatrix g.1 = 1 := by
    ext s t
    let x : Space N := WithLp.toLp 2 fun c => WithLp.toLp 2 fun u =>
      WithLp.toLp 2 fun _ => if u = t then 1 else 0
    have he := congrArg (fun A : Module.End ℂ (Space N) =>
      A x b s (HistoryModuleRepresentation.base 0)) hg
    change source N g.1 (relative N g.2 x) b s (HistoryModuleRepresentation.base 0) =
      x b s (HistoryModuleRepresentation.base 0) at he
    rw [source_apply] at he
    simp only [hrelative] at he
    change (∑ u : Spin, sourceMatrix g.1 s u * (if u = t then 1 else 0)) =
      (if s = t then 1 else 0) at he
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Matrix.one_apply] using he
  have hp : ((g.1.1 : Operations.SourceSpinCorner.Mat2),
      (g.1.2 : Operations.SourceSpinCorner.Mat2)) = 1 :=
    Operations.SourceCliffordComplex.complexPairMap_injective
      (hM.trans (map_one Operations.SourceCliffordComplex.complexPairMap).symm)
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

theorem relative_kernel {N : ℕ} (hN : 0 < N) (z : Circle) :
    relative N z = 1 ↔ z = 1 := by
  constructor
  · intro hz
    let b : Roots N := ⟨1, by omega⟩
    have he : HistoryJointCircleAction.action 1 0 1 z = 1 := by
      apply LinearMap.ext
      intro v
      let x : Space N := PiLp.single 2 b v
      have hx := congrArg (fun A : Module.End ℂ (Space N) => A x b) hz
      simpa [x, b] using hx
    have hs := HistoryJointCircleAction.action_sectorProjection 1 0 1 z (true, .inl 0)
    rw [he, one_mul] at hs
    have hzero : ((z : ℂ) - 1) •
        HistoryChargeSectors.sectorProjection 1 (true, .inl 0) = 0 := by
      simpa only [HistoryJointChargeLattice.detail_left, zpow_one,
        sub_smul, one_smul] using sub_eq_zero.mpr hs.symm
    exact Circle.coe_eq_one.mp (sub_eq_zero.mp
      ((smul_eq_zero.mp hzero).resolve_right
        (HistoryChargeSectors.sectorProjection_ne_zero (by decide) _)))
  · rintro rfl
    exact map_one (relative N)

theorem representation_kernel {N : ℕ} (hN : 0 < N) (g : Presentation) :
    representation N g = 1 ↔ g = 1 := by
  constructor
  · intro hg
    have hs := joint_kernel_source N g hg
    have hr : relative N g.2 = 1 := by
      simpa only [representation, MonoidHom.coe_mk, OneHom.coe_mk, hs, map_one, one_mul]
        using hg
    exact Prod.ext hs ((relative_kernel hN g.2).mp hr)
  · rintro rfl
    exact map_one (representation N)

theorem representation_faithful {N : ℕ} (hN : 0 < N) :
    Function.Injective (representation N) := by
  intro g h he
  apply mul_inv_eq_one.mp
  apply (representation_kernel hN (g * h⁻¹)).mp
  rw [map_mul, he, ← map_mul, mul_inv_cancel, map_one]

abbrev StateUnitary (N : ℕ) := Space N ≃ₗᵢ[ℂ] Space N
abbrev SourceFactor := Operations.SourceSpinCornerGroup.SU2

def unitary (N : ℕ) (g : Presentation) : StateUnitary N :=
  (Operations.UnitaryRepresentation.representationLinearEquiv
    (representation N) g).isometryOfInner (representation_inner N g)

@[simp] theorem unitary_apply (N : ℕ) (g : Presentation) (x : Space N) :
    unitary N g x = representation N g x := rfl

def unitaryRepresentation (N : ℕ) : Presentation →* StateUnitary N where
  toFun := unitary N
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation N 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation N (g * h) x = representation N g (representation N h x)
    rw [map_mul]
    rfl

theorem unitaryRepresentation_faithful {N : ℕ} (hN : 0 < N) :
    Function.Injective (unitaryRepresentation N) := by
  intro g h he
  apply representation_faithful hN
  apply LinearMap.ext
  intro x
  exact congrArg (fun U : StateUnitary N => U x) he

def sourceInclusion : Frame →* Presentation where
  toFun g := (g, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

def circleInclusion : Circle →* Presentation where
  toFun z := (1, z)
  map_one' := rfl
  map_mul' _ _ := by simp

def leftOperators (N : ℕ) : SourceFactor →* StateUnitary N :=
  (unitaryRepresentation N).comp
    (sourceInclusion.comp HistoryGeneratedFrameGroup.leftInclusion)

def rightOperators (N : ℕ) : SourceFactor →* StateUnitary N :=
  (unitaryRepresentation N).comp
    (sourceInclusion.comp HistoryGeneratedFrameGroup.rightInclusion)

def circleOperators (N : ℕ) : Circle →* StateUnitary N :=
  (unitaryRepresentation N).comp circleInclusion

theorem presentation_factorization (g : Presentation) :
    sourceInclusion (HistoryGeneratedFrameGroup.leftInclusion g.1.1) *
      sourceInclusion (HistoryGeneratedFrameGroup.rightInclusion g.1.2) *
      circleInclusion g.2 = g := by
  simp [sourceInclusion, circleInclusion,
    HistoryGeneratedFrameGroup.leftInclusion, HistoryGeneratedFrameGroup.rightInclusion]

theorem presentation_factorization_unique (l r : SourceFactor) (z : Circle)
    (g : Presentation)
    (h : sourceInclusion (HistoryGeneratedFrameGroup.leftInclusion l) *
      sourceInclusion (HistoryGeneratedFrameGroup.rightInclusion r) * circleInclusion z = g) :
    l = g.1.1 ∧ r = g.1.2 ∧ z = g.2 := by
  simpa [sourceInclusion, circleInclusion, HistoryGeneratedFrameGroup.leftInclusion,
    HistoryGeneratedFrameGroup.rightInclusion, Prod.ext_iff, and_assoc] using h

abbrev GeneratedGroup (N : ℕ) := (unitaryRepresentation N).range

theorem left_mem_generated (N : ℕ) (g : SourceFactor) :
    leftOperators N g ∈ GeneratedGroup N :=
  ⟨sourceInclusion (HistoryGeneratedFrameGroup.leftInclusion g), rfl⟩

theorem right_mem_generated (N : ℕ) (g : SourceFactor) :
    rightOperators N g ∈ GeneratedGroup N :=
  ⟨sourceInclusion (HistoryGeneratedFrameGroup.rightInclusion g), rfl⟩

theorem circle_mem_generated (N : ℕ) (z : Circle) :
    circleOperators N z ∈ GeneratedGroup N := ⟨circleInclusion z, rfl⟩

def factorClosure (N : ℕ) : Subgroup (StateUnitary N) :=
  Subgroup.closure (Set.range (leftOperators N) ∪ Set.range (rightOperators N) ∪
    Set.range (circleOperators N))

theorem factorClosure_eq_generated (N : ℕ) : factorClosure N = GeneratedGroup N := by
  apply le_antisymm
  · apply (Subgroup.closure_le (GeneratedGroup N)).2
    rintro U ((⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨g, rfl⟩)
    · exact ⟨sourceInclusion (HistoryGeneratedFrameGroup.leftInclusion g), rfl⟩
    · exact ⟨sourceInclusion (HistoryGeneratedFrameGroup.rightInclusion g), rfl⟩
    · exact ⟨circleInclusion g, rfl⟩
  · rintro U ⟨g, rfl⟩
    have hl : leftOperators N g.1.1 ∈ factorClosure N :=
      Subgroup.subset_closure (Or.inl (Or.inl ⟨g.1.1, rfl⟩))
    have hr : rightOperators N g.1.2 ∈ factorClosure N :=
      Subgroup.subset_closure (Or.inl (Or.inr ⟨g.1.2, rfl⟩))
    have hc : circleOperators N g.2 ∈ factorClosure N :=
      Subgroup.subset_closure (Or.inr ⟨g.2, rfl⟩)
    have hm := (factorClosure N).mul_mem ((factorClosure N).mul_mem hl hr) hc
    have he : leftOperators N g.1.1 * rightOperators N g.1.2 * circleOperators N g.2 =
        unitaryRepresentation N g := by
      change unitaryRepresentation N
        (sourceInclusion (HistoryGeneratedFrameGroup.leftInclusion g.1.1)) *
        unitaryRepresentation N
          (sourceInclusion (HistoryGeneratedFrameGroup.rightInclusion g.1.2)) *
        unitaryRepresentation N (circleInclusion g.2) = _
      rw [← map_mul, ← map_mul, presentation_factorization]
    exact he ▸ hm

theorem generated_least (N : ℕ) (H : Subgroup (StateUnitary N))
    (hl : ∀ g, leftOperators N g ∈ H) (hr : ∀ g, rightOperators N g ∈ H)
    (hc : ∀ z, circleOperators N z ∈ H) : GeneratedGroup N ≤ H := by
  rw [← factorClosure_eq_generated]
  apply (Subgroup.closure_le H).2
  rintro U ((⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨g, rfl⟩)
  · exact hl g
  · exact hr g
  · exact hc g

def presentationEquiv {N : ℕ} (hN : 0 < N) : Presentation ≃* GeneratedGroup N :=
  MulEquiv.ofBijective (unitaryRepresentation N).rangeRestrict
    ⟨fun _ _ h => unitaryRepresentation_faithful hN (congrArg Subtype.val h),
      by rintro ⟨U, g, rfl⟩; exact ⟨g, rfl⟩⟩

/-- Actual state transitions detect the complete group cocycle. There is no
unobserved central relift in this faithful state representation. -/
theorem transition_cocycle_iff {N : ℕ} (hN : 0 < N)
    (g h k : Presentation) :
    unitaryRepresentation N g * unitaryRepresentation N h =
      unitaryRepresentation N k ↔ g * h = k := by
  rw [← map_mul]
  exact (unitaryRepresentation_faithful hN).eq_iff

/-- The defect is evaluated in the single full group presentation. -/
def tripleDefect (g h k : Presentation) : Presentation := g * h * k⁻¹

theorem tripleDefect_phase (g h k : Presentation) :
    (tripleDefect g h k).2 = g.2 * h.2 * k.2⁻¹ := rfl

theorem tripleDefect_kernel_iff {N : ℕ} (hN : 0 < N) (g h k : Presentation) :
    unitaryRepresentation N (tripleDefect g h k) = 1 ↔ g * h = k := by
  rw [tripleDefect, map_mul, map_inv, mul_inv_eq_one,
    (unitaryRepresentation_faithful hN).eq_iff]

structure Conclusions : Prop where
  full_coordinate_equivalence : ∀ N (x y : HistoryCliffordAction.Space N),
    inner ℂ (coordinates N x) (coordinates N y) = inner ℂ x y
  joint_commutation : ∀ N g z, source N g * relative N z = relative N z * source N g
  complete_response : ∀ N g (x y : Space N),
    inner ℂ (representation N g x) (representation N g y) = inner ℂ x y
  calculated_kernel : ∀ N, 0 < N → ∀ g, representation N g = 1 ↔ g = 1
  faithful_joint_action : ∀ N, 0 < N → Function.Injective (representation N)
  least_complete_closure : ∀ N, factorClosure N = GeneratedGroup N
  unique_full_presentation : ∀ N (hN : 0 < N), Function.Bijective (presentationEquiv hN)
  complete_transition_cocycle : ∀ N, 0 < N → ∀ g h k,
    unitaryRepresentation N g * unitaryRepresentation N h =
      unitaryRepresentation N k ↔ g * h = k

theorem generated : Conclusions where
  full_coordinate_equivalence := fun N => (coordinates N).inner_map_map
  joint_commutation := source_relative_commute
  complete_response := representation_inner
  calculated_kernel := fun _ => representation_kernel
  faithful_joint_action := fun _ => representation_faithful
  least_complete_closure := factorClosure_eq_generated
  unique_full_presentation := fun _ hN => (presentationEquiv hN).bijective
  complete_transition_cocycle := fun _ => transition_cocycle_iff

end GeneratedFoundations.Arithmetic.HistoryCompleteSourceGroup
