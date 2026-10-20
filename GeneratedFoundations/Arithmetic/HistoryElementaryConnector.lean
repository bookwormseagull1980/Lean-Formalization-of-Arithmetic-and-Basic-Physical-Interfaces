module

public import GeneratedFoundations.Arithmetic.HistorySourceNaturality
public import GeneratedFoundations.Geometry.SourceScalarResponse

/-!
# Classification of complete odd responses on history--phase fibres

The input is an arbitrary matrix on the full arithmetic carrier. Oddness,
self-adjointness and commutation with the actual history matrix algebra are
tested on that input. They force one uniform off-diagonal source matrix;
reversal compatibility then gives one unique doublet. No block factorization
or cancellation of mixed terms is included in the input type.

The resulting operator acts on both source sectors, on the original Gaussian
realization and on its Haar realization. Occupation parity belongs to the
arithmetic factor and is preserved, rather than identified with chirality.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryElementaryConnector

open HistoryCliffordAction
open HistoryComplexConnector (Mat2 connector)
open GeneratedFoundations.Operations

abbrev Spinor := ReversalRealConnector.Spinor

def upper (N : ℕ) (A : Algebra N) : HistorySourceNaturality.SourceMatrix N :=
  fun i j => A (i.1, Sum.inl i.2) (j.1, Sum.inr j.2)

def Natural (N : ℕ) (A : Algebra N) : Prop :=
  ∀ B : Matrix (HistoryLabel N) (HistoryLabel N) ℂ,
    A * historyLift N B = historyLift N B * A

def Odd (N : ℕ) (A : Algebra N) : Prop :=
  sourceGrading N * A + A * sourceGrading N = 0

def Elementary (N : ℕ) (A : Algebra N) : Prop :=
  Natural N A ∧ A.conjTranspose = A ∧ Odd N A ∧
    HistorySourceNaturality.ReversalCompatible N (upper N A)

theorem natural_upper (N : ℕ) (A : Algebra N) (hA : Natural N A) :
    HistorySourceNaturality.Natural N (upper N A) := by
  intro B
  ext ⟨h, i⟩ ⟨k, j⟩
  have he := congrArg (fun T : Algebra N => T (h, Sum.inl i) (k, Sum.inr j)) (hA B)
  simpa [upper, historyLift, HistorySourceNaturality.historyAction,
    Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply] using he

theorem odd_positive_zero (N : ℕ) (A : Algebra N) (hA : Odd N A)
    (h k : HistoryLabel N) (i j : Fin 2) :
    A (h, Sum.inl i) (k, Sum.inl j) = 0 := by
  have he := congrArg (fun T : Algebra N => T (h, Sum.inl i) (k, Sum.inl j)) hA
  simp [sourceGrading, SourceCliffordConnector.grading, Matrix.mul_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply] at he
  exact he

theorem odd_negative_zero (N : ℕ) (A : Algebra N) (hA : Odd N A)
    (h k : HistoryLabel N) (i j : Fin 2) :
    A (h, Sum.inr i) (k, Sum.inr j) = 0 := by
  have he := congrArg (fun T : Algebra N => T (h, Sum.inr i) (k, Sum.inr j)) hA
  simp [sourceGrading, SourceCliffordConnector.grading, Matrix.mul_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply] at he
  exact he

@[simp] theorem upper_connector (N : ℕ) (M : Mat2) :
    upper N (connector N M) = HistorySourceNaturality.spinLift N M := by
  ext ⟨h, i⟩ ⟨k, j⟩
  rfl

/-- The lower block is forced by the adjoint equation; it is not selected
independently when forming a response. -/
theorem reconstruct (N : ℕ) (A : Algebra N) (M : Mat2)
    (hstar : A.conjTranspose = A) (hodd : Odd N A)
    (hupper : upper N A = HistorySourceNaturality.spinLift N M) :
    A = connector N M := by
  ext ⟨h, i⟩ ⟨k, j⟩
  rcases i with i | i <;> rcases j with j | j
  · rw [odd_positive_zero N A hodd]
    simp [connector, SourceCliffordComplex.connector]
  · exact congrArg (fun T : HistorySourceNaturality.SourceMatrix N => T (h, i) (k, j)) hupper
  · have hs := congrArg (fun T : Algebra N => T (h, Sum.inr i) (k, Sum.inl j)) hstar
    have hu := congrArg (fun T : HistorySourceNaturality.SourceMatrix N => T (k, j) (h, i)) hupper
    rw [← hs]
    change star (A (k, Sum.inl j) (h, Sum.inr i)) = _
    change A (k, Sum.inl j) (h, Sum.inr i) = _ at hu
    rw [hu]
    by_cases hk : h = k <;>
      simp [HistorySourceNaturality.spinLift, connector, SourceCliffordComplex.connector,
        Matrix.conjTranspose_apply, hk, eq_comm]
  · rw [odd_negative_zero N A hodd]
    simp [connector, SourceCliffordComplex.connector]

theorem natural_selfAdjoint_odd_iff (N : ℕ) (A : Algebra N) :
    Natural N A ∧ A.conjTranspose = A ∧ Odd N A ↔
      ∃! M : Mat2, A = connector N M := by
  constructor
  · rintro ⟨hn, hs, ho⟩
    obtain ⟨M, hM, _⟩ :=
      (HistorySourceNaturality.natural_iff_existsUnique_source N (upper N A)).mp
        (natural_upper N A hn)
    have he := reconstruct N A M hs ho hM
    refine ⟨M, he, ?_⟩
    intro K hK
    exact HistoryComplexConnector.connector_injective N (hK.symm.trans he)
  · rintro ⟨M, rfl, _⟩
    exact ⟨fun B => HistoryComplexConnector.connector_historyLift N M B,
      HistoryComplexConnector.connector_adjoint N M, HistoryComplexConnector.connector_odd N M⟩

def scalarConnector (N : ℕ) (v : Spinor) : Algebra N :=
  connector N (ReversalRealConnector.connectorOfDoublet v)

theorem scalarConnector_injective (N : ℕ) : Function.Injective (scalarConnector N) :=
  (HistoryComplexConnector.connector_injective N).comp
    ReversalRealConnector.connectorOfDoublet_injective

/-- The complete operator conditions, before any representation change,
determine exactly one source doublet. -/
theorem elementary_iff_unique_doublet (N : ℕ) (A : Algebra N) :
    Elementary N A ↔ ∃! v : Spinor, A = scalarConnector N v := by
  constructor
  · rintro ⟨hn, hs, ho, hr⟩
    obtain ⟨v, hv, _⟩ :=
      (HistorySourceNaturality.natural_reversal_iff_unique_doublet N (upper N A)).mp
        ⟨natural_upper N A hn, hr⟩
    have he := reconstruct N A _ hs ho hv
    refine ⟨v, he, ?_⟩
    intro w hw
    exact scalarConnector_injective N (hw.symm.trans he)
  · rintro ⟨v, rfl, _⟩
    refine ⟨fun B => HistoryComplexConnector.connector_historyLift N _ B,
      HistoryComplexConnector.connector_adjoint N _,
      HistoryComplexConnector.connector_odd N _, ?_⟩
    rw [scalarConnector, upper_connector]
    exact (HistorySourceNaturality.spinLift_reversalCompatible_iff N _).mpr
      (ReversalRealConnector.connectorOfDoublet_reversalReal v)

theorem canonical_elementary (N : ℕ) (v : Spinor) : Elementary N (scalarConnector N v) :=
  (elementary_iff_unique_doublet N _).mpr
    ⟨v, rfl, fun _w hw => scalarConnector_injective N hw.symm⟩

theorem hermite_intertwines (N : ℕ) (v : Spinor) (x : Space N) :
    hermiteIsometry N (action N (scalarConnector N v) x) =
      HistoryComplexConnector.hermiteConnector N (ReversalRealConnector.connectorOfDoublet v)
        (hermiteIsometry N x) :=
  HistoryComplexConnector.hermiteConnector_intertwines N _ x

theorem haar_intertwines (N : ℕ) (v : Spinor) (x : Space N) :
    HistoryHaarResponse.fullAction N (scalarConnector N v) (HistoryHaarResponse.fullUnitary N x) =
      HistoryHaarResponse.fullUnitary N (action N (scalarConnector N v) x) :=
  HistoryHaarResponse.fullAction_intertwines N _ x

theorem complete_observation (N : ℕ) (v : Spinor) (x y : Space N) :
    inner ℂ (HistoryHaarResponse.fullUnitary N x)
      (HistoryHaarResponse.fullAction N (scalarConnector N v)
        (HistoryHaarResponse.fullUnitary N y)) =
      inner ℂ x (action N (scalarConnector N v) y) :=
  HistoryHaarResponse.complete_response_invariant N _ x y

abbrev Frame := Geometry.SourceScalarResponse.Frame

/-- Independent source frames act on the complete arithmetic carrier. -/
def frame (N : ℕ) : Frame →* Algebra N where
  toFun g := HistoryEvenResponse.matrix N ((g.1 : Mat2), (g.2 : Mat2))
  map_one' := HistoryEvenResponse.matrix_one N
  map_mul' g k := by
    change HistoryEvenResponse.matrix N
      (((g.1 : Mat2) * (k.1 : Mat2)), ((g.2 : Mat2) * (k.2 : Mat2))) = _
    exact HistoryEvenResponse.matrix_mul N ((g.1 : Mat2), (g.2 : Mat2))
      ((k.1 : Mat2), (k.2 : Mat2))

theorem frame_adjoint (N : ℕ) (g : Frame) :
    (frame N g).conjTranspose = frame N g⁻¹ := by
  rw [show frame N g = HistoryEvenResponse.matrix N ((g.1 : Mat2), (g.2 : Mat2)) from rfl,
    HistoryEvenResponse.matrix_adjoint]
  rfl

theorem frame_adjoint_mul (N : ℕ) (g : Frame) :
    (frame N g).conjTranspose * frame N g = 1 := by
  rw [frame_adjoint, ← map_mul, inv_mul_cancel, map_one]

theorem frame_mul_adjoint (N : ℕ) (g : Frame) :
    frame N g * (frame N g).conjTranspose = 1 := by
  rw [frame_adjoint, ← map_mul, mul_inv_cancel, map_one]

/-- Both chiral blocks transform together; the lower adjoint block is
retained throughout the congruence. -/
theorem scalarConnector_covariant (N : ℕ) (g : Frame) (v : Spinor) :
    frame N g * scalarConnector N v * (frame N g).conjTranspose =
      scalarConnector N (Geometry.SourceScalarResponse.frameDoublet g v) := by
  change HistoryEvenResponse.matrix N _ * connector N _ *
    (HistoryEvenResponse.matrix N _).conjTranspose = connector N _
  rw [HistoryEvenResponse.connector_covariance,
    Geometry.SourceScalarResponse.connectorOfDoublet_frameDoublet]
  rfl

theorem scalarConnector_intertwines (N : ℕ) (g : Frame) (v : Spinor) :
    frame N g * scalarConnector N v =
      scalarConnector N (Geometry.SourceScalarResponse.frameDoublet g v) * frame N g := by
  rw [← scalarConnector_covariant]
  rw [mul_assoc (frame N g * scalarConnector N v), frame_adjoint_mul, mul_one]

section Local

variable {ι X : Type*}

def CompatibleDoublets (U : ι → Set X) (g : ι → ι → X → Frame)
    (v : ι → X → Spinor) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j →
    v i x = Geometry.SourceScalarResponse.frameDoublet (g i j x) (v j x)

def CompatibleConnectors (N : ℕ) (U : ι → Set X) (g : ι → ι → X → Frame)
    (A : ι → X → Algebra N) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j →
    A i x = frame N (g i j x) * A j x * (frame N (g i j x)).conjTranspose

/-- The operator overlap law is equivalent to its unique source-coordinate
law; no off-diagonal coefficient is lost on overlaps. -/
theorem compatibleConnectors_iff_doublets (N : ℕ) (U : ι → Set X)
    (g : ι → ι → X → Frame) (v : ι → X → Spinor) :
    CompatibleConnectors N U g (fun i x => scalarConnector N (v i x)) ↔
      CompatibleDoublets U g v := by
  unfold CompatibleConnectors CompatibleDoublets
  simp only [scalarConnector_covariant, (scalarConnector_injective N).eq_iff]

/-- Arbitrary elementary operators on the patches determine the doublets.
Their unused values outside the patches are not part of the uniqueness claim. -/
theorem local_elementary_doublets (N : ℕ) (U : ι → Set X)
    (g : ι → ι → X → Frame) (A : ι → X → Algebra N)
    (he : ∀ i x, x ∈ U i → Elementary N (A i x))
    (hg : CompatibleConnectors N U g A) :
    ∃ v : ι → X → Spinor,
      (∀ i x, x ∈ U i → A i x = scalarConnector N (v i x)) ∧
      CompatibleDoublets U g v ∧
      ∀ w : ι → X → Spinor,
        (∀ i x, x ∈ U i → A i x = scalarConnector N (w i x)) →
        ∀ i x, x ∈ U i → w i x = v i x := by
  classical
  have hex (i : ι) (x : X) (hx : x ∈ U i) :
      ∃ v : Spinor, A i x = scalarConnector N v :=
    ((elementary_iff_unique_doublet N (A i x)).mp (he i x hx)).exists
  let v : ι → X → Spinor := fun i x =>
    if hx : x ∈ U i then Classical.choose (hex i x hx) else 0
  have hv (i : ι) (x : X) (hx : x ∈ U i) : A i x = scalarConnector N (v i x) := by
    simp only [v, dite_eq_left hx]
    exact Classical.choose_spec (hex i x hx)
  refine ⟨v, hv, ?_, ?_⟩
  · apply (compatibleConnectors_iff_doublets N U g v).mp
    intro i j x hi hj
    change scalarConnector N (v i x) =
      frame N (g i j x) * scalarConnector N (v j x) * (frame N (g i j x)).conjTranspose
    rw [← hv i x hi, ← hv j x hj]
    exact hg i j x hi hj
  · intro w hw i x hx
    exact scalarConnector_injective N ((hw i x hx).symm.trans (hv i x hx))

theorem doublet_two_routes (U : ι → Set X) (g : ι → ι → X → Frame)
    (hg : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      g i j x * g j k x = g i k x)
    (i j k : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k)
    (v : Spinor) :
    Geometry.SourceScalarResponse.frameDoublet (g i j x)
      (Geometry.SourceScalarResponse.frameDoublet (g j k x) v) =
        Geometry.SourceScalarResponse.frameDoublet (g i k x) v := by
  rw [← Geometry.SourceScalarResponse.frameDoublet_mul, hg i j k x hi hj hk]

def CompatibleSections (N : ℕ) (U : ι → Set X) (g : ι → ι → X → Frame)
    (x : ι → X → Space N) : Prop :=
  ∀ i j z, z ∈ U i → z ∈ U j → x i z = action N (frame N (g i j z)) (x j z)

theorem scalarConnector_apply_frame (N : ℕ) (g : Frame) (v : Spinor) (x : Space N) :
    action N (scalarConnector N (Geometry.SourceScalarResponse.frameDoublet g v))
        (action N (frame N g) x) =
      action N (frame N g) (action N (scalarConnector N v) x) := by
  have h := congrArg (action N) (scalarConnector_intertwines N g v)
  rw [map_mul, map_mul] at h
  exact (LinearMap.congr_fun h x).symm

/-- Application of the complete connector preserves the actual state-section
overlap law, including both source sectors. -/
theorem compatibleDoublets_apply_sections (N : ℕ) {U : ι → Set X}
    {g : ι → ι → X → Frame} {v : ι → X → Spinor} {x : ι → X → Space N}
    (hv : CompatibleDoublets U g v) (hx : CompatibleSections N U g x) :
    CompatibleSections N U g (fun i z => action N (scalarConnector N (v i z)) (x i z)) := by
  intro i j z hi hj
  change action N (scalarConnector N (v i z)) (x i z) =
    action N (frame N (g i j z)) (action N (scalarConnector N (v j z)) (x j z))
  rw [hv i j z hi hj, hx i j z hi hj]
  exact scalarConnector_apply_frame N _ _ _

end Local

/-- Source frames over the actual retained history--phase labels. -/
abbrev FrameField (N : ℕ) := HistoryLabel N → Frame

def canonicalFrame (N : ℕ) : FrameField N := fun _ => 1

def transition (N : ℕ) (g : FrameField N) (h k : HistoryLabel N) : Frame :=
  (g h)⁻¹ * g k

@[simp] theorem transition_self (N : ℕ) (g : FrameField N) (h : HistoryLabel N) :
    transition N g h h = 1 := inv_mul_cancel _

theorem transition_cocycle (N : ℕ) (g : FrameField N) (h k l : HistoryLabel N) :
    transition N g h k * transition N g k l = transition N g h l := by
  simp [transition, mul_assoc]

def localDoublet (N : ℕ) (g : FrameField N) (v : Spinor) (h : HistoryLabel N) : Spinor :=
  Geometry.SourceScalarResponse.frameDoublet (g h)⁻¹ v

theorem localDoublet_overlap (N : ℕ) (g : FrameField N) (v : Spinor)
    (h k : HistoryLabel N) :
    localDoublet N g v h =
      Geometry.SourceScalarResponse.frameDoublet (transition N g h k) (localDoublet N g v k) := by
  simp only [localDoublet, transition, ← Geometry.SourceScalarResponse.frameDoublet_mul]
  simp [mul_assoc]

theorem actual_connector_overlap (N : ℕ) (g : FrameField N) (v : Spinor)
    (h k : HistoryLabel N) :
    scalarConnector N (localDoublet N g v h) =
      frame N (transition N g h k) * scalarConnector N (localDoublet N g v k) *
        (frame N (transition N g h k)).conjTranspose := by
  rw [scalarConnector_covariant, ← localDoublet_overlap]

@[simp] theorem canonical_localDoublet (N : ℕ) (v : Spinor) (h : HistoryLabel N) :
    localDoublet N (canonicalFrame N) v h = v := by
  simp [localDoublet, canonicalFrame]

structure Conclusions : Prop where
  complete_classification : ∀ N A, Natural N A ∧ A.conjTranspose = A ∧ Odd N A ↔
    ∃! M, A = connector N M
  unique_elementary_response : ∀ N A, Elementary N A ↔ ∃! v, A = scalarConnector N v
  faithful_response : ∀ N, Function.Injective (scalarConnector N)
  actual_source_conditions : ∀ N v, Elementary N (scalarConnector N v)
  full_frame_covariance : ∀ N g v,
    frame N g * scalarConnector N v * (frame N g).conjTranspose =
      scalarConnector N (Geometry.SourceScalarResponse.frameDoublet g v)
  actual_frame_overlap : ∀ N (g : FrameField N) v h k,
    scalarConnector N (localDoublet N g v h) =
      frame N (transition N g h k) * scalarConnector N (localDoublet N g v k) *
        (frame N (transition N g h k)).conjTranspose
  original_gaussian_transport : ∀ N v (x : Space N),
    hermiteIsometry N (action N (scalarConnector N v) x) =
      HistoryComplexConnector.hermiteConnector N (ReversalRealConnector.connectorOfDoublet v)
        (hermiteIsometry N x)
  haar_observation : ∀ N v (x y : Space N),
    inner ℂ (HistoryHaarResponse.fullUnitary N x)
      (HistoryHaarResponse.fullAction N (scalarConnector N v)
        (HistoryHaarResponse.fullUnitary N y)) =
      inner ℂ x (action N (scalarConnector N v) y)

theorem generated : Conclusions where
  complete_classification := natural_selfAdjoint_odd_iff
  unique_elementary_response := elementary_iff_unique_doublet
  faithful_response := scalarConnector_injective
  actual_source_conditions := canonical_elementary
  full_frame_covariance := scalarConnector_covariant
  actual_frame_overlap := actual_connector_overlap
  original_gaussian_transport := hermite_intertwines
  haar_observation := complete_observation

end GeneratedFoundations.Arithmetic.HistoryElementaryConnector
