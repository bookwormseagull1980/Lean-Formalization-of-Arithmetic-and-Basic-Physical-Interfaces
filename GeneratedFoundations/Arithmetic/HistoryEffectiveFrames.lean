module

public import GeneratedFoundations.Arithmetic.HistoryElementaryConnector
public import GeneratedFoundations.Geometry.SourceFrameQuotient
public import GeneratedFoundations.Geometry.EffectiveActionCocycle
public import GeneratedFoundations.Operations.UnitaryRepresentation

/-!
# Effective source frames on complete arithmetic responses

The actual history--phase state representation is faithful. Its simultaneous
source sign acts as minus identity on states, while conjugation makes that
sign invisible on elementary response operators. These are two different
actions on two explicitly constructed carriers.

The effective response group is obtained from the calculated two-element
kernel. Its faithful action on the complete elementary operators is transported
through their already proved unique doublet coordinates. Every such operator
retains both source sectors and every arithmetic label.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryEffectiveFrames

open HistoryCliffordAction HistoryElementaryConnector
open GeneratedFoundations.Operations
open Geometry.SourceScalarResponse (frameDoublet)

abbrev EffectiveFrame := Geometry.SourceFrameQuotient.EffectiveFrame

theorem frame_injective (N : ℕ) : Function.Injective (frame N) := by
  intro g h he
  have hp := HistoryEvenResponse.matrix_injective N he
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hp)
  · exact Subtype.ext (congrArg Prod.snd hp)

theorem frame_kernel (N : ℕ) (g : Frame) : frame N g = 1 ↔ g = 1 := by
  rw [← (frame N).map_one]
  exact (frame_injective N).eq_iff

theorem frame_action_faithful (N : ℕ) :
    Function.Injective (fun g => action N (frame N g)) :=
  (action N).injective.comp (frame_injective N)

def stateResponse (N : ℕ) : Frame →* Module.End ℂ (Space N) :=
  (action N).toMonoidHom.comp (frame N)

theorem stateResponse_adjoint (N : ℕ) (g : Frame) :
    (stateResponse N g).adjoint = stateResponse N g⁻¹ := by
  change (action N (frame N g)).adjoint = action N (frame N g⁻¹)
  rw [action_adjoint, frame_adjoint]

theorem stateResponse_inner (N : ℕ) (g : Frame) (x y : Space N) :
    inner ℂ (stateResponse N g x) (stateResponse N g y) = inner ℂ x y :=
  UnitaryRepresentation.representation_inner_of_adjoint (stateResponse N)
    (stateResponse_adjoint N) g x y

def stateUnitary (N : ℕ) (g : Frame) : Space N ≃ₗᵢ[ℂ] Space N :=
  (UnitaryRepresentation.representationLinearEquiv (stateResponse N) g).isometryOfInner
    (stateResponse_inner N g)

@[simp] theorem stateUnitary_apply (N : ℕ) (g : Frame) (x : Space N) :
    stateUnitary N g x = action N (frame N g) x := rfl

@[simp] theorem stateUnitary_symm_apply (N : ℕ) (g : Frame) (x : Space N) :
    (stateUnitary N g).symm x = stateResponse N g⁻¹ x := rfl

theorem stateResponse_norm (N : ℕ) (g : Frame) (x : Space N) :
    ‖stateResponse N g x‖ = ‖x‖ := (stateUnitary N g).norm_map x

theorem stateResponse_mem_unitary (N : ℕ) (g : Frame) :
    stateResponse N g ∈ unitary (Module.End ℂ (Space N)) :=
  UnitaryRepresentation.representation_mem_unitary_of_adjoint (stateResponse N)
    (stateResponse_adjoint N) g

def unitaryRepresentation (N : ℕ) : Frame →* (Space N ≃ₗᵢ[ℂ] Space N) where
  toFun := stateUnitary N
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change stateResponse N 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    change stateResponse N (g * h) x = stateResponse N g (stateResponse N h x)
    rw [map_mul]
    rfl

theorem unitaryRepresentation_faithful (N : ℕ) :
    Function.Injective (unitaryRepresentation N) := by
  intro g h he
  apply frame_action_faithful N
  apply LinearMap.ext
  intro x
  exact congrArg (fun U : Space N ≃ₗᵢ[ℂ] Space N => U x) he

/-- On the full carrier the simultaneous sign is retained as minus identity. -/
theorem frame_centralSign (N : ℕ) :
    frame N Geometry.SourceFrameQuotient.centralSign = -(1 : Algebra N) := by
  change HistoryEvenResponse.matrix N
    ((Geometry.SourceFrameQuotient.negative : HistoryComplexConnector.Mat2),
      (Geometry.SourceFrameQuotient.negative : HistoryComplexConnector.Mat2)) = _
  rw [Geometry.SourceFrameQuotient.negative_matrix]
  ext ⟨h, i⟩ ⟨k, j⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp [HistoryEvenResponse.matrix, SourceCliffordComplex.complexPairMap,
      Matrix.one_apply, eq_comm]
  all_goals by_cases hh : h = k <;> by_cases hij : i = j <;> simp [hh, hij]

theorem state_centralSign (N : ℕ) (x : Space N) :
    action N (frame N Geometry.SourceFrameQuotient.centralSign) x = -x := by
  rw [frame_centralSign, map_neg, map_one]
  rfl

def conjugate (N : ℕ) (g : Frame) (A : Algebra N) : Algebra N :=
  frame N g * A * (frame N g).conjTranspose

@[simp] theorem conjugate_one (N : ℕ) (A : Algebra N) : conjugate N 1 A = A := by
  simp [conjugate]

theorem conjugate_mul (N : ℕ) (g h : Frame) (A : Algebra N) :
    conjugate N (g * h) A = conjugate N g (conjugate N h A) := by
  simp [conjugate, map_mul, Matrix.conjTranspose_mul, mul_assoc]

theorem conjugate_add (N : ℕ) (g : Frame) (A B : Algebra N) :
    conjugate N g (A + B) = conjugate N g A + conjugate N g B := by
  simp [conjugate, mul_add, add_mul]

theorem conjugate_smul (N : ℕ) (g : Frame) (c : ℂ) (A : Algebra N) :
    conjugate N g (c • A) = c • conjugate N g A := by
  simp [conjugate]

theorem conjugate_product (N : ℕ) (g : Frame) (A B : Algebra N) :
    conjugate N g (A * B) = conjugate N g A * conjugate N g B := by
  symm
  simp only [conjugate, mul_assoc]
  rw [← mul_assoc (frame N g).conjTranspose, frame_adjoint_mul, one_mul]

theorem conjugate_adjoint (N : ℕ) (g : Frame) (A : Algebra N) :
    (conjugate N g A).conjTranspose = conjugate N g A.conjTranspose := by
  simp [conjugate, Matrix.conjTranspose_mul, mul_assoc]

def responseInner (N : ℕ) (A B : Algebra N) : ℂ := Matrix.trace (A.conjTranspose * B)

theorem conjugate_responseInner (N : ℕ) (g : Frame) (A B : Algebra N) :
    responseInner N (conjugate N g A) (conjugate N g B) = responseInner N A B := by
  rw [responseInner, conjugate_adjoint, ← conjugate_product]
  unfold conjugate
  rw [Matrix.trace_mul_cycle, frame_adjoint_mul, one_mul]
  rfl

theorem conjugate_elementary (N : ℕ) (g : Frame) (A : Algebra N)
    (hA : Elementary N A) : Elementary N (conjugate N g A) := by
  obtain ⟨v, rfl, _⟩ := (elementary_iff_unique_doublet N A).mp hA
  rw [conjugate, scalarConnector_covariant]
  exact canonical_elementary N _

theorem conjugate_centralSign (N : ℕ) (A : Algebra N) :
    conjugate N Geometry.SourceFrameQuotient.centralSign A = A := by
  simp [conjugate, frame_centralSign]

theorem conjugate_central_relift (N : ℕ) (g : Frame) (A : Algebra N) :
    conjugate N (Geometry.SourceFrameQuotient.centralSign * g) A = conjugate N g A := by
  simp [conjugate, map_mul, frame_centralSign, mul_assoc]

/-- The complete response kernel is derived from actual operator equality. -/
theorem elementary_response_kernel (N : ℕ) (g : Frame) :
    (∀ A : Algebra N, Elementary N A → conjugate N g A = A) ↔
      g = 1 ∨ g = Geometry.SourceFrameQuotient.centralSign := by
  rw [← Geometry.SourceFrameQuotient.response_kernel_iff]
  constructor
  · intro hg v
    apply scalarConnector_injective N
    exact (scalarConnector_covariant N g v).symm.trans
      (hg (scalarConnector N v) (canonical_elementary N v))
  · intro hg A hA
    obtain ⟨v, rfl, _⟩ := (elementary_iff_unique_doublet N A).mp hA
    rw [conjugate, scalarConnector_covariant, hg]

abbrev ElementarySpace (N : ℕ) := {A : Algebra N // Elementary N A}

/-- Coordinates are inferred from the full operator, not supplied as an
additional field in its type. -/
def coordinateEquiv (N : ℕ) : Spinor ≃ ElementarySpace N :=
  Equiv.ofBijective (fun v => ⟨scalarConnector N v, canonical_elementary N v⟩)
    ⟨fun _ _ h => scalarConnector_injective N (congrArg Subtype.val h), by
      intro A
      obtain ⟨v, hv, _⟩ := (elementary_iff_unique_doublet N A.1).mp A.2
      exact ⟨v, Subtype.ext hv.symm⟩⟩

@[simp] theorem coordinateEquiv_apply (N : ℕ) (v : Spinor) :
    (coordinateEquiv N v).1 = scalarConnector N v := rfl

def effectiveAction (N : ℕ) : EffectiveFrame →* Equiv.Perm (ElementarySpace N) where
  toFun q := (coordinateEquiv N).permCongr (Geometry.SourceFrameQuotient.effectiveResponse q)
  map_one' := by
    apply Equiv.ext
    intro A
    simp [Equiv.permCongr]
  map_mul' q r := by
    apply Equiv.ext
    intro A
    simp [Equiv.permCongr]

theorem effectiveAction_faithful (N : ℕ) : Function.Injective (effectiveAction N) := by
  intro q r h
  apply Geometry.SourceFrameQuotient.effectiveResponse_faithful
  apply Equiv.ext
  intro v
  apply (coordinateEquiv N).injective
  have hv := Equiv.congr_fun h (coordinateEquiv N v)
  simpa [effectiveAction, Equiv.permCongr] using hv

theorem effectiveAction_quotient (N : ℕ) (g : Frame) (A : ElementarySpace N) :
    ((effectiveAction N (Geometry.SourceFrameQuotient.quotientMap g)) A).1 =
      conjugate N g A.1 := by
  obtain ⟨v, rfl⟩ := (coordinateEquiv N).surjective A
  change ((coordinateEquiv N).permCongr
    (Geometry.SourceFrameQuotient.effectiveResponse
      (Geometry.SourceFrameQuotient.quotientMap g)) (coordinateEquiv N v)).1 = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Geometry.SourceFrameQuotient.effectiveResponse_quotientMap]
  exact (scalarConnector_covariant N g v).symm

theorem effectiveAction_unique (N : ℕ)
    (R : EffectiveFrame →* Equiv.Perm (ElementarySpace N))
    (hR : ∀ g A, (R (Geometry.SourceFrameQuotient.quotientMap g) A).1 =
      conjugate N g A.1) : R = effectiveAction N := by
  apply MonoidHom.ext
  intro q
  apply Equiv.ext
  intro A
  induction q using Quotient.inductionOn' with
  | h g => exact Subtype.ext ((hR g A).trans (effectiveAction_quotient N g A).symm)

/-- Conjugation acts on every full matrix, not only on the elementary family. -/
def conjugation (N : ℕ) : Frame →* Equiv.Perm (Algebra N) where
  toFun g :=
    { toFun := conjugate N g
      invFun := conjugate N g⁻¹
      left_inv A := by rw [← conjugate_mul, inv_mul_cancel, conjugate_one]
      right_inv A := by rw [← conjugate_mul, mul_inv_cancel, conjugate_one] }
  map_one' := by
    apply Equiv.ext
    exact conjugate_one N
  map_mul' g h := by
    apply Equiv.ext
    exact conjugate_mul N g h

theorem conjugation_kernel (N : ℕ) (g : Frame) :
    conjugation N g = 1 ↔ g ∈ Geometry.SourceFrameQuotient.response.ker := by
  rw [Geometry.SourceFrameQuotient.mem_response_kernel]
  constructor
  · intro hg
    exact (elementary_response_kernel N g).mp (fun A _ => Equiv.congr_fun hg A)
  · rintro (rfl | rfl)
    · exact (conjugation N).map_one
    · apply Equiv.ext
      exact conjugate_centralSign N

def effectiveConjugation (N : ℕ) : EffectiveFrame →* Equiv.Perm (Algebra N) :=
  QuotientGroup.lift Geometry.SourceFrameQuotient.response.ker (conjugation N)
    (fun g hg => (conjugation_kernel N g).mpr hg)

@[simp] theorem effectiveConjugation_quotient (N : ℕ) (g : Frame) (A : Algebra N) :
    effectiveConjugation N (Geometry.SourceFrameQuotient.quotientMap g) A =
      conjugate N g A := rfl

theorem effectiveConjugation_inner (N : ℕ) (q : EffectiveFrame) (A B : Algebra N) :
    responseInner N (effectiveConjugation N q A) (effectiveConjugation N q B) =
      responseInner N A B := by
  induction q using Quotient.inductionOn' with
  | h g => exact conjugate_responseInner N g A B

theorem effectiveConjugation_scalar (N : ℕ) (q : EffectiveFrame) (v : Spinor) :
    effectiveConjugation N q (scalarConnector N v) =
      scalarConnector N (Geometry.SourceFrameQuotient.effectiveResponse q v) := by
  induction q using Quotient.inductionOn' with
  | h g => exact scalarConnector_covariant N g v

theorem effectiveConjugation_faithful (N : ℕ) :
    Function.Injective (effectiveConjugation N) := by
  intro q r h
  apply Geometry.SourceFrameQuotient.effectiveResponse_faithful
  apply Equiv.ext
  intro v
  apply scalarConnector_injective N
  rw [← effectiveConjugation_scalar, ← effectiveConjugation_scalar, h]

theorem conjugation_eq_iff_central_difference (N : ℕ) (g h : Frame) :
    conjugation N g = conjugation N h ↔
      g * h⁻¹ = 1 ∨ g * h⁻¹ = Geometry.SourceFrameQuotient.centralSign := by
  rw [← Geometry.SourceFrameQuotient.mem_response_kernel, ← conjugation_kernel]
  exact (Geometry.EffectiveActionCocycle.mapped_mul_inv_eq_one_iff
    (conjugation N) g h).symm

theorem effectiveConjugation_unique (N : ℕ) (R : EffectiveFrame →* Equiv.Perm (Algebra N))
    (hR : ∀ g A, R (Geometry.SourceFrameQuotient.quotientMap g) A = conjugate N g A) :
    R = effectiveConjugation N := by
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h g => exact Equiv.ext (hR g)

theorem effectiveConjugation_in_generated (N : ℕ) (q : EffectiveFrame) :
    effectiveConjugation N q ∈ (conjugation N).range := by
  induction q using Quotient.inductionOn' with
  | h g => exact ⟨g, rfl⟩

theorem effectiveConjugation_complete (N : ℕ) : Function.Surjective
    ((effectiveConjugation N).codRestrict (conjugation N).range
      (effectiveConjugation_in_generated N)) := by
  rintro ⟨A, g, rfl⟩
  exact ⟨Geometry.SourceFrameQuotient.quotientMap g, rfl⟩

def effectiveEquivRange (N : ℕ) : EffectiveFrame ≃* (conjugation N).range :=
  Geometry.EffectiveActionCocycle.realizationEquiv (conjugation N) (effectiveConjugation N)
    (effectiveConjugation_in_generated N) (effectiveConjugation_faithful N)
    (effectiveConjugation_complete N)

theorem effectiveEquivRange_apply (N : ℕ) (q : EffectiveFrame) :
    (effectiveEquivRange N q : Equiv.Perm (Algebra N)) = effectiveConjugation N q := rfl

/-- Every faithful comparison with exactly the generated complete response
image has one unique action-compatible identification with that image. -/
theorem generated_realization_unique (N : ℕ) {K : Type*} [Group K]
    (ρ : K →* Equiv.Perm (Algebra N)) (hin : ∀ k, ρ k ∈ (conjugation N).range)
    (hfaithful : Function.Injective ρ)
    (hcomplete : Function.Surjective (ρ.codRestrict (conjugation N).range hin)) :
    ∃! e : K ≃* (conjugation N).range,
      ∀ k, (e k : Equiv.Perm (Algebra N)) = ρ k := by
  refine ⟨Geometry.EffectiveActionCocycle.realizationEquiv (conjugation N) ρ
    hin hfaithful hcomplete, fun _ => rfl, ?_⟩
  intro e he
  exact Geometry.EffectiveActionCocycle.realizationEquiv_unique (conjugation N) ρ
    hin hfaithful hcomplete e he

/-- The response quotient is not a quotient of the full state action: the
state retains the simultaneous central sign. -/
theorem stateResponse_not_descend (N : ℕ) :
    ¬ ∃ R : EffectiveFrame →* Module.End ℂ (Space N),
      ∀ g, R (Geometry.SourceFrameQuotient.quotientMap g) = stateResponse N g := by
  rintro ⟨R, hR⟩
  have hq : Geometry.SourceFrameQuotient.quotientMap
      Geometry.SourceFrameQuotient.centralSign = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr
      ((Geometry.SourceFrameQuotient.mem_response_kernel _).mpr (Or.inr rfl))
  have he : stateResponse N Geometry.SourceFrameQuotient.centralSign =
      stateResponse N 1 := by
    calc
      _ = R (Geometry.SourceFrameQuotient.quotientMap
          Geometry.SourceFrameQuotient.centralSign) := (hR _).symm
      _ = R 1 := congrArg R hq
      _ = R (Geometry.SourceFrameQuotient.quotientMap 1) := by simp only [map_one]
      _ = _ := hR 1
  exact Geometry.SourceFrameQuotient.centralSign_ne_one
    (frame_action_faithful N he)

theorem full_response_intertwines (N : ℕ) (g : Frame) (A : Algebra N) (x : Space N) :
    action N (conjugate N g A) (stateUnitary N g x) =
      stateUnitary N g (action N A x) := by
  have hm : conjugate N g A * frame N g = frame N g * A := by
    rw [conjugate, mul_assoc (frame N g * A), frame_adjoint_mul, mul_one]
  have he := congrArg (action N) hm
  rw [map_mul, map_mul] at he
  exact LinearMap.congr_fun he x

theorem complete_response_inner (N : ℕ) (g : Frame) (A : Algebra N) (x y : Space N) :
    inner ℂ (stateUnitary N g x) (action N (conjugate N g A) (stateUnitary N g y)) =
      inner ℂ x (action N A y) := by
  rw [full_response_intertwines]
  exact (stateUnitary N g).inner_map_map x (action N A y)

section Overlaps

variable {ι X : Type*}

open Geometry.EffectiveActionCocycle

abbrev LiftData (ι X : Type*) := ι → ι → X → Frame

def quotientTransition (g : LiftData ι X) (i j : ι) (x : X) : EffectiveFrame :=
  Geometry.SourceFrameQuotient.quotientMap (g i j x)

def responseTransition (N : ℕ) (g : LiftData ι X) (i j : ι) (x : X) :
    Equiv.Perm (Algebra N) := effectiveConjugation N (quotientTransition g i j x)

/-- Only the actual generated full-operator image is inverted. An arbitrary
permutation of operator coordinates is not a source transition. -/
abbrev RealizedResponse (N : ℕ) := (conjugation N).range

def quotientFromRealized (N : ℕ) (t : ι → ι → X → RealizedResponse N) :
    ι → ι → X → EffectiveFrame := fun i j x => (effectiveEquivRange N).symm (t i j x)

theorem quotientFromRealized_action (N : ℕ) (t : ι → ι → X → RealizedResponse N)
    (i j : ι) (x : X) :
    effectiveConjugation N (quotientFromRealized N t i j x) =
      (t i j x : Equiv.Perm (Algebra N)) :=
  congrArg Subtype.val ((effectiveEquivRange N).apply_symm_apply (t i j x))

theorem realizedCocycle_iff (N : ℕ) (U : ι → Set X)
    (t : ι → ι → X → RealizedResponse N) :
    CocycleOn U (quotientFromRealized N t) ↔
      CocycleOn U (fun i j x => (t i j x : Equiv.Perm (Algebra N))) := by
  simpa only [quotientFromRealized_action] using
    map_cocycle_iff (effectiveConjugation N) (effectiveConjugation_faithful N)
      U (quotientFromRealized N t)

theorem quotientFromRealized_unique (N : ℕ) (t : ι → ι → X → RealizedResponse N)
    (q : ι → ι → X → EffectiveFrame)
    (hq : ∀ i j x, effectiveConjugation N (q i j x) =
      (t i j x : Equiv.Perm (Algebra N))) : q = quotientFromRealized N t := by
  funext i j x
  exact effectiveConjugation_faithful N
    ((hq i j x).trans (quotientFromRealized_action N t i j x).symm)

def CentralDefects (U : ι → Set X) (g : LiftData ι X) : Prop :=
  ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    tripleDefect g i j k x ∈ Geometry.SourceFrameQuotient.response.ker

theorem tripleDefect_two_signs (g : LiftData ι X) (i j k : ι) (x : X) :
    tripleDefect g i j k x ∈ Geometry.SourceFrameQuotient.response.ker ↔
      tripleDefect g i j k x = 1 ∨
        tripleDefect g i j k x = Geometry.SourceFrameQuotient.centralSign :=
  Geometry.SourceFrameQuotient.mem_response_kernel _

theorem centralDefects_iff_quotientCocycle (U : ι → Set X) (g : LiftData ι X) :
    CentralDefects U g ↔ CocycleOn U (quotientTransition g) :=
  (kernelDefects_iff_actionCocycle Geometry.SourceFrameQuotient.response U g).trans
    (quotientCocycle_iff_actionCocycle Geometry.SourceFrameQuotient.response U g).symm

theorem centralDefects_iff_responseCocycle (N : ℕ) (U : ι → Set X) (g : LiftData ι X) :
    CentralDefects U g ↔ CocycleOn U (responseTransition N g) :=
  (centralDefects_iff_quotientCocycle U g).trans
    (map_cocycle_iff (effectiveConjugation N) (effectiveConjugation_faithful N) U
      (quotientTransition g))

theorem response_two_routes (N : ℕ) {U : ι → Set X} {g : LiftData ι X}
    (hg : CentralDefects U g) (i j k : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) (A : Algebra N) :
    responseTransition N g i j x (responseTransition N g j k x A) =
      responseTransition N g i k x A :=
  Equiv.congr_fun ((centralDefects_iff_responseCocycle N U g).mp hg i j k x hi hj hk) A

/-- A change of lift is drawn from the computed kernel, not from a new phase
law. Its value may vary on each overlap. -/
def centralRelift (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) : LiftData ι X :=
  fun i j x => (z i j x : Frame) * g i j x

theorem centralRelift_quotient
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) (i j : ι) (x : X) :
    quotientTransition (centralRelift z g) i j x = quotientTransition g i j x :=
  quotient_relift Geometry.SourceFrameQuotient.response _ _ (z i j x).property

theorem centralRelift_response (N : ℕ)
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) (i j : ι) (x : X) :
    responseTransition N (centralRelift z g) i j x = responseTransition N g i j x := by
  rw [responseTransition, responseTransition, centralRelift_quotient]

theorem centralRelift_defects_iff (U : ι → Set X)
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) : CentralDefects U (centralRelift z g) ↔ CentralDefects U g := by
  rw [centralDefects_iff_quotientCocycle, centralDefects_iff_quotientCocycle]
  simp only [CocycleOn, centralRelift_quotient]

theorem compatibleSections_passive {N : ℕ} {U : ι → Set X} {g : LiftData ι X}
    {s : ι → X → Space N} (hs : CompatibleSections N U g s)
    (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    s j x = stateUnitary N (g i j x)⁻¹ (s i x) := by
  rw [hs i j x hi hj]
  change s j x = (stateResponse N (g i j x)⁻¹ * stateResponse N (g i j x)) (s j x)
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem compatibleSections_inner {N : ℕ} {U : ι → Set X} {g : LiftData ι X}
    {s r : ι → X → Space N} (hs : CompatibleSections N U g s)
    (hr : CompatibleSections N U g r) (i j : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) :
    inner ℂ (s i x) (r i x) = inner ℂ (s j x) (r j x) := by
  rw [hs i j x hi hj, hr i j x hi hj]
  exact stateResponse_inner N _ _ _

theorem compatibleSections_norm {N : ℕ} {U : ι → Set X} {g : LiftData ι X}
    {s : ι → X → Space N} (hs : CompatibleSections N U g s)
    (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) : ‖s i x‖ = ‖s j x‖ := by
  rw [hs i j x hi hj]
  exact (stateUnitary N _).norm_map _

end Overlaps

structure Conclusions : Prop where
  full_state_faithful : ∀ N, Function.Injective (fun g => action N (frame N g))
  actual_response_kernel : ∀ N g,
    (∀ A : Algebra N, Elementary N A → conjugate N g A = A) ↔
      g = 1 ∨ g = Geometry.SourceFrameQuotient.centralSign
  effective_response_faithful : ∀ N, Function.Injective (effectiveAction N)
  response_descends : ∀ N g A,
    ((effectiveAction N (Geometry.SourceFrameQuotient.quotientMap g)) A).1 =
      conjugate N g A.1
  retained_state_sign : ∀ N (x : Space N),
    action N (frame N Geometry.SourceFrameQuotient.centralSign) x = -x
  all_responses_faithful : ∀ N, Function.Injective (effectiveConjugation N)
  coherent_observations : ∀ N g A (x y : Space N),
    inner ℂ (stateUnitary N g x) (action N (conjugate N g A) (stateUnitary N g y)) =
      inner ℂ x (action N A y)

theorem generated : Conclusions where
  full_state_faithful := frame_action_faithful
  actual_response_kernel := elementary_response_kernel
  effective_response_faithful := effectiveAction_faithful
  response_descends := effectiveAction_quotient
  retained_state_sign := state_centralSign
  all_responses_faithful := effectiveConjugation_faithful
  coherent_observations := complete_response_inner

end GeneratedFoundations.Arithmetic.HistoryEffectiveFrames
