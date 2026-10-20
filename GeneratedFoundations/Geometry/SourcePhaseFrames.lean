module

public import GeneratedFoundations.Geometry.HermitianFrames
public import GeneratedFoundations.Geometry.SourceFactorBases
public import Mathlib.Analysis.Complex.Circle

/-!
# Phase frames of the actual retained source line

The retained line is the degree-zero Haar carrier, already identified with the
alternating source square. Its fixed orthonormal basis gives the coefficient of
an arbitrary vector. The complete one-dimensional expansion shows that every
complex unitary change of frame is multiplication by one unique circle phase.
This is a classification of arbitrary unitary maps, not a scalar ansatz.

On actual Hermitian bundle charts the same phase describes the passive
transition, its inverse on components, and the triple-overlap cocycle. This is
the local frame freedom of the line. It does not assert a new action of the
unlocalized source group, or assume a global trivialization of the line bundle.
-/

@[expose] public section

noncomputable section

open scoped Bundle
open GeneratedFoundations.Geometry.SourceJointResponse (L)
open GeneratedFoundations.Geometry.SourceFactorBases (lineBasis)

namespace GeneratedFoundations.Geometry.SourcePhaseFrames

open HermitianFrames

/-- The coefficient uses the same actual source-line basis as the original source factor. -/
def coordinate : L →L[ℂ] ℂ := innerSL ℂ (lineBasis 0)

@[simp] theorem coordinate_apply (v : L) : coordinate v = inner ℂ (lineBasis 0) v := rfl

@[simp] theorem coordinate_basis : coordinate (lineBasis 0) = 1 := by
  simp [coordinate]

/-- Completeness of the one-element source basis, not a hypothesis on the vector. -/
theorem coordinate_synthesis (v : L) : coordinate v • lineBasis 0 = v := by
  simpa only [Fin.sum_univ_one, coordinate_apply] using lineBasis.sum_repr' v

theorem coordinate_norm (v : L) : ‖coordinate v‖ = ‖v‖ := by
  have hv := congrArg (fun w : L => ‖w‖) (coordinate_synthesis v)
  simpa only [norm_smul, lineBasis.norm_eq_one, mul_one] using hv

theorem coordinate_injective : Function.Injective coordinate := by
  intro v w h
  calc
    v = coordinate v • lineBasis 0 := (coordinate_synthesis v).symm
    _ = coordinate w • lineBasis 0 := congrArg (fun z : ℂ => z • lineBasis 0) h
    _ = w := coordinate_synthesis w

/-- A prescribed circle phase acts unitarily on the actual source line. -/
def phaseAction (z : Circle) : L ≃ₗᵢ[ℂ] L where
  toFun v := (z : ℂ) • v
  invFun v := (z⁻¹ : Circle) • v
  left_inv v := by simp [Circle.smul_def, smul_smul]
  right_inv v := by simp [Circle.smul_def, smul_smul]
  map_add' v w := smul_add (z : ℂ) v w
  map_smul' a v := smul_comm (z : ℂ) a v
  norm_map' v := by simp [norm_smul]

@[simp] theorem phaseAction_apply (z : Circle) (v : L) :
    phaseAction z v = (z : ℂ) • v := rfl

theorem phase_norm (g : L ≃ₗᵢ[ℂ] L) :
    ‖coordinate (g (lineBasis 0))‖ = 1 := by
  rw [coordinate_norm, g.norm_map, lineBasis.norm_eq_one]

/-- Extract the phase from an unrestricted complex unitary map. -/
def phase (g : L ≃ₗᵢ[ℂ] L) : Circle :=
  ⟨coordinate (g (lineBasis 0)), mem_sphere_zero_iff_norm.mpr (phase_norm g)⟩

@[simp] theorem phase_coe (g : L ≃ₗᵢ[ℂ] L) :
    (phase g : ℂ) = coordinate (g (lineBasis 0)) := rfl

theorem unitary_eq_phase_smul (g : L ≃ₗᵢ[ℂ] L) (v : L) :
    g v = (phase g : ℂ) • v := by
  have hb : g (lineBasis 0) = (phase g : ℂ) • lineBasis 0 :=
    (coordinate_synthesis (g (lineBasis 0))).symm
  calc
    g v = g (coordinate v • lineBasis 0) :=
      congrArg g (coordinate_synthesis v).symm
    _ = coordinate v • g (lineBasis 0) := map_smul g (coordinate v) (lineBasis 0)
    _ = coordinate v • ((phase g : ℂ) • lineBasis 0) := congrArg (fun w => coordinate v • w) hb
    _ = (phase g : ℂ) • (coordinate v • lineBasis 0) :=
      smul_comm (coordinate v) (phase g : ℂ) (lineBasis 0)
    _ = (phase g : ℂ) • v := by rw [coordinate_synthesis]

@[simp] theorem phaseAction_phase (g : L ≃ₗᵢ[ℂ] L) : phaseAction (phase g) = g := by
  apply LinearIsometryEquiv.ext
  intro v
  exact (unitary_eq_phase_smul g v).symm

@[simp] theorem phase_phaseAction (z : Circle) : phase (phaseAction z) = z := by
  apply Circle.ext
  change coordinate (phaseAction z (lineBasis 0)) = (z : ℂ)
  simp only [phaseAction_apply, map_smul, coordinate_basis, smul_eq_mul, mul_one]

theorem phase_mul (g h : L ≃ₗᵢ[ℂ] L) : phase (g * h) = phase g * phase h := by
  apply Circle.ext
  change coordinate (g (h (lineBasis 0))) = (phase g : ℂ) * (phase h : ℂ)
  rw [unitary_eq_phase_smul g (h (lineBasis 0))]
  exact map_smul coordinate (phase g : ℂ) (h (lineBasis 0))

/-- The entire unitary group of the actual source line is the circle group. -/
def phaseEquiv : (L ≃ₗᵢ[ℂ] L) ≃* Circle where
  toFun := phase
  invFun := phaseAction
  left_inv := phaseAction_phase
  right_inv := phase_phaseAction
  map_mul' := phase_mul

@[simp] theorem phase_one : phase (1 : L ≃ₗᵢ[ℂ] L) = 1 := phaseEquiv.map_one

@[simp] theorem phase_symm (g : L ≃ₗᵢ[ℂ] L) : phase g.symm = (phase g)⁻¹ :=
  phaseEquiv.map_inv g

/-- The scalar form is concluded for every vector, with a unique circle parameter. -/
theorem unitary_existsUnique_phase (g : L ≃ₗᵢ[ℂ] L) :
    ∃! z : Circle, ∀ v : L, g v = (z : ℂ) • v := by
  refine ⟨phase g, unitary_eq_phase_smul g, ?_⟩
  intro z hz
  apply Circle.ext
  change (z : ℂ) = coordinate (g (lineBasis 0))
  have h := congrArg coordinate (hz (lineBasis 0))
  simpa only [map_smul, coordinate_basis, smul_eq_mul, mul_one] using h.symm

section LocalCharts

variable {M : Type*} [TopologicalSpace M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [TopologicalSpace (Bundle.TotalSpace L E)]

variable (e f k : Bundle.Trivialization L (π L E))
  [e.IsLinear ℂ] [f.IsLinear ℂ] [k.IsLinear ℂ]

def transitionPhase (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) : Circle :=
  phase (transition e f he hf x hx hy)

theorem transition_eq_phase_smul (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : L) :
    transition e f he hf x hx hy v = (transitionPhase e f he hf x hx hy : ℂ) • v :=
  unitary_eq_phase_smul (transition e f he hf x hx hy) v

theorem transition_existsUnique_phase
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    ∃! z : Circle, ∀ v : L, transition e f he hf x hx hy v = (z : ℂ) • v :=
  unitary_existsUnique_phase (transition e f he hf x hx hy)

/-- In the passive convention the new frame is the old frame multiplied by the phase. -/
theorem frame_phase (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : L) :
    frame f hf x hy v = (transitionPhase e f he hf x hx hy : ℂ) • frame e he x hx v := by
  calc
    frame f hf x hy v = frame e he x hx (transition e f he hf x hx hy v) :=
      (frame_transition e f he hf x hx hy v).symm
    _ = frame e he x hx ((transitionPhase e f he hf x hx hy : ℂ) • v) := by
      rw [transition_eq_phase_smul]
    _ = _ := map_smul (frame e he x hx) _ v

/-- Vectors are unchanged; their new components acquire the inverse phase. -/
theorem passive_components (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : E x) :
    (frame f hf x hy).symm v =
      ((transitionPhase e f he hf x hx hy)⁻¹ : Circle) • (frame e he x hx).symm v := by
  rw [HermitianFrames.passive_components e f he hf x hx hy]
  simpa only [phase_symm, Circle.smul_def, transitionPhase] using
    unitary_eq_phase_smul (transition e f he hf x hx hy).symm ((frame e he x hx).symm v)

def localComponent (he : IsHermitianChart e) (x : M) (hx : x ∈ e.baseSet)
    (v : E x) : ℂ := coordinate ((frame e he x hx).symm v)

theorem passive_component (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : E x) :
    localComponent f hf x hy v =
      (((transitionPhase e f he hf x hx hy)⁻¹ : Circle) : ℂ) *
        localComponent e he x hx v := by
  exact (congrArg coordinate (passive_components e f he hf x hx hy v)).trans
    (map_smul coordinate (((transitionPhase e f he hf x hx hy)⁻¹ : Circle) : ℂ)
      ((frame e he x hx).symm v))

@[simp] theorem transitionPhase_self (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) : transitionPhase e e he he x hx hx = 1 := by
  change phase (transition e e he he x hx hx) = 1
  rw [transition_self, phase_one]

theorem transitionPhase_inverse (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    transitionPhase f e hf he x hy hx = (transitionPhase e f he hf x hx hy)⁻¹ := by
  change phase (transition f e hf he x hy hx) = (phase (transition e f he hf x hx hy))⁻¹
  rw [← transition_inverse e f he hf x hx hy, phase_symm]

theorem transitionPhase_cocycle
    (he : IsHermitianChart e) (hf : IsHermitianChart f) (hk : IsHermitianChart k)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (hz : x ∈ k.baseSet) :
    transitionPhase e f he hf x hx hy * transitionPhase f k hf hk x hy hz =
      transitionPhase e k he hk x hx hz := by
  change phase (transition e f he hf x hx hy) * phase (transition f k hf hk x hy hz) = _
  rw [← phase_mul, transition_cocycle]
  rfl

/-- The extracted phase is the coefficient of the actual bundle overlap operator. -/
theorem transitionPhase_eq_overlapCoordinate
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    (transitionPhase e f he hf x hx hy : ℂ) =
      coordinate (overlapOperator e f x (lineBasis 0)) := by
  change coordinate (transition e f he hf x hx hy (lineBasis 0)) = _
  rw [overlapOperator_eq_transition e f he hf x hx hy]
  rfl

end LocalCharts

end GeneratedFoundations.Geometry.SourcePhaseFrames
