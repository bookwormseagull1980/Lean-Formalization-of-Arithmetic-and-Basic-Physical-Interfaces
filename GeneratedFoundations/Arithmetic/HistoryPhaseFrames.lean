module

public import GeneratedFoundations.Arithmetic.HistoryPhaseAction
public import GeneratedFoundations.Geometry.HermitianFrames

/-!
# Actual unitary frames on the generated history--phase fibres

The base is the positive generated root, and its fibre is the complete
history--phase coefficient space. The native phase action supplies concrete
unitary frames and relative transitions. Arbitrary unitary matrices are also
realized uniquely on that same fibre, using its complete orthonormal basis.

Frame choices in comparison statements are observation coordinates, not
additional source data. The canonical frame is the internally available
zero phase. States and response operators are transported together, so the
observed sesquilinear response retains all off-diagonal coefficients.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryPhaseFrames

open HistoryModuleRepresentation HistoryPhaseAction

abbrev Total := (n : ℕ) × Space n
abbrev PhaseField := (n : ℕ) → ZMod (n + 1)

def projection (v : Total) : ℕ := v.1 + 1

def canonicalFrame : PhaseField := fun _ => 0

def gaugeAction (g : PhaseField) (v : Total) : Total :=
  ⟨v.1, unitary v.1 (g v.1) v.2⟩

theorem gaugeAction_projection (g : PhaseField) (v : Total) :
    projection (gaugeAction g v) = projection v := rfl

theorem gaugeAction_norm (g : PhaseField) (v : Total) :
    ‖(gaugeAction g v).2‖ = ‖v.2‖ := (unitary v.1 (g v.1)).norm_map v.2

theorem gaugeAction_canonical (v : Total) : gaugeAction canonicalFrame v = v := by
  rcases v with ⟨n, x⟩
  simp only [gaugeAction, canonicalFrame, unitary_zero]

theorem gaugeAction_inverse (g : PhaseField) (v : Total) :
    gaugeAction (fun n => -g n) (gaugeAction g v) = v := by
  rcases v with ⟨n, x⟩
  change (⟨n, unitary n (-g n) (unitary n (g n) x)⟩ : Total) = ⟨n, x⟩
  rw [unitary_add, neg_add_cancel, unitary_zero]

/-- Relative phase sends the second frame's components to the first frame. -/
def transition (n : ℕ) (p q : ZMod (n + 1)) : ZMod (n + 1) := q - p

theorem transition_self (n : ℕ) (p : ZMod (n + 1)) : transition n p p = 0 := by
  simp [transition]

theorem transition_inverse (n : ℕ) (p q : ZMod (n + 1)) :
    -transition n p q = transition n q p := by simp [transition]

theorem transition_cocycle (n : ℕ) (p q r : ZMod (n + 1)) :
    transition n p q + transition n q r = transition n p r := by
  simp [transition]

theorem frame_transition (n : ℕ) (p q : ZMod (n + 1)) (x : Space n) :
    unitary n p (unitary n (transition n p q) x) = unitary n q x := by
  rw [unitary_add]
  congr 1
  simp [transition]

theorem transition_unique (n : ℕ) (p q z : ZMod (n + 1))
    (hz : ∀ x : Space n, unitary n p (unitary n z x) = unitary n q x) :
    z = transition n p q := by
  have h : p + z = q := unitary_faithful n (LinearIsometryEquiv.ext
    (fun x => (unitary_add n p z x).symm.trans (hz x)))
  change z = q - p
  rw [← h]
  simp

def components (n : ℕ) (p : ZMod (n + 1)) (x : Space n) : Space n :=
  (unitary n p).symm x

theorem frame_components (n : ℕ) (p : ZMod (n + 1)) (x : Space n) :
    unitary n p (components n p x) = x :=
  (unitary n p).apply_symm_apply x

theorem components_transition (n : ℕ) (p q : ZMod (n + 1)) (x : Space n) :
    components n p x = unitary n (transition n p q) (components n q x) := by
  apply (unitary n p).injective
  rw [frame_components, frame_transition, frame_components]

theorem components_passive (n : ℕ) (p q : ZMod (n + 1)) (x : Space n) :
    components n q x =
      (unitary n (transition n p q)).symm (components n p x) := by
  apply (unitary n (transition n p q)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (components_transition n p q x).symm

/-- The basis indexes the complete actual fibre, with its derived size. -/
def basis (n : ℕ) : OrthonormalBasis (Fin (Fintype.card (Index n))) ℂ (Space n) :=
  (EuclideanSpace.basisFun (Index n) ℂ).reindex (Fintype.equivFin (Index n))

def frameMatrix (n : ℕ) (g : Space n ≃ₗᵢ[ℂ] Space n) :=
  Geometry.HermitianFrames.frameMatrix (basis n) g

theorem frameMatrix_unitary (n : ℕ) (g : Space n ≃ₗᵢ[ℂ] Space n) :
    frameMatrix n g ∈ Matrix.unitaryGroup (Fin (Fintype.card (Index n))) ℂ :=
  Geometry.HermitianFrames.frameMatrix_unitary (basis n) g

theorem frameMatrix_existsUnique (n : ℕ)
    (M : Matrix (Fin (Fintype.card (Index n))) (Fin (Fintype.card (Index n))) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin (Fintype.card (Index n))) ℂ) :
    ∃! g : Space n ≃ₗᵢ[ℂ] Space n, frameMatrix n g = M :=
  Geometry.HermitianFrames.frameMatrix_existsUnique (basis n) M hM

theorem frameMatrix_specialUnitary_iff (n : ℕ) (g : Space n ≃ₗᵢ[ℂ] Space n) :
    frameMatrix n g ∈ Matrix.specialUnitaryGroup (Fin (Fintype.card (Index n))) ℂ ↔
      (frameMatrix n g).det = 1 :=
  Geometry.HermitianFrames.frameMatrix_specialUnitary_iff (basis n) g

/-- Conjugation transports the complete response, not just its diagonal. -/
def response (n : ℕ) (p : ZMod (n + 1)) (A : Algebra n) :
    Module.End ℂ (Space n) :=
  (unitary n p).toLinearEquiv.conjAlgEquiv ℂ (representation n A)

theorem response_intertwines (n : ℕ) (p : ZMod (n + 1)) (A : Algebra n)
    (x : Space n) :
    response n p A (unitary n p x) = unitary n p (representation n A x) := by
  change unitary n p (representation n A ((unitary n p).symm (unitary n p x))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem complete_response_invariant (n : ℕ) (p : ZMod (n + 1)) (A : Algebra n)
    (x y : Space n) :
    inner ℂ (unitary n p x) (response n p A (unitary n p y)) =
      inner ℂ x (representation n A y) := by
  rw [response_intertwines]
  exact (unitary n p).inner_map_map x (representation n A y)

structure Conclusions : Prop where
  canonical_action : ∀ v, gaugeAction canonicalFrame v = v
  preserves_base : ∀ g v, projection (gaugeAction g v) = projection v
  preserves_norm : ∀ g v, ‖(gaugeAction g v).2‖ = ‖v.2‖
  exact_transitions : ∀ n p q r,
    transition n p q + transition n q r = transition n p r
  unique_transitions : ∀ n p q z,
    (∀ x : Space n, unitary n p (unitary n z x) = unitary n q x) →
      z = transition n p q
  all_unitary_matrices : ∀ n M,
    M ∈ Matrix.unitaryGroup (Fin (Fintype.card (Index n))) ℂ →
      ∃! g : Space n ≃ₗᵢ[ℂ] Space n, frameMatrix n g = M
  coherent_covariance : ∀ n p A (x y : Space n),
    inner ℂ (unitary n p x) (response n p A (unitary n p y)) =
      inner ℂ x (representation n A y)

theorem generated : Conclusions where
  canonical_action := gaugeAction_canonical
  preserves_base := gaugeAction_projection
  preserves_norm := gaugeAction_norm
  exact_transitions := transition_cocycle
  unique_transitions := transition_unique
  all_unitary_matrices := frameMatrix_existsUnique
  coherent_covariance := complete_response_invariant

end GeneratedFoundations.Arithmetic.HistoryPhaseFrames
