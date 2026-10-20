module

public import GeneratedFoundations.Arithmetic.HistoryElementaryConnector
public import GeneratedFoundations.Geometry.SourceReversalIsometry

/-!
# Antiunitary reversal on complete arithmetic source fibres

The source reversal acts on the two source coordinates at every retained
history--phase label. Its antiunitarity is calculated on the complete
coefficient inner product. The Gaussian--Haar map intertwines this operation
with the original source reversal, without averaging labels or sectors.

The direct sum contains both source chiral sectors. Its reversal preserves
each sector and commutes with independent generated source frames and with
every elementary connector. Occupation parity and ordered history reversal
remain separate arithmetic operations; no identification with either is used.
All comparison maps below act on the already generated arithmetic carrier.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryReversalIsometry

open HistoryCliffordAction
open HistoryComplexConnector (Mat2 sectorAction connector)
open GeneratedFoundations.Operations

abbrev reversal := HistorySourceNaturality.reversal

theorem reversal_add (N : ℕ) (x y : SectorSpace N) :
    reversal N (x + y) = reversal N x + reversal N y := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  exact congrFun (ReversalRealConnector.reversal_add
    (fun j => x (h, j)) (fun j => y (h, j))) i

theorem reversal_inner (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (reversal N x) (reversal N y) = inner ℂ y x := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  simp [reversal, HistorySourceNaturality.reversal, ReversalRealConnector.reversal,
    Fin.sum_univ_two]
  ring

theorem reversal_norm (N : ℕ) (x : SectorSpace N) : ‖reversal N x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (reversal N x),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) x, reversal_inner]

theorem reversal_neg (N : ℕ) (x : SectorSpace N) : reversal N (-x) = -reversal N x :=
  map_neg (AddMonoidHom.mk' (reversal N) (reversal_add N)) x

/-- The actual labelwise source operation, with its derived norm and inverse. -/
def sectorReversal (N : ℕ) : SectorSpace N ≃ₗᵢ⋆[ℂ] SectorSpace N where
  toFun := reversal N
  invFun x := -reversal N x
  left_inv x := by
    change -HistorySourceNaturality.reversal N (HistorySourceNaturality.reversal N x) = x
    rw [HistorySourceNaturality.reversal_square, neg_neg]
  right_inv x := by
    change reversal N (-reversal N x) = x
    rw [reversal_neg]
    change -HistorySourceNaturality.reversal N (HistorySourceNaturality.reversal N x) = x
    rw [HistorySourceNaturality.reversal_square, neg_neg]
  map_add' := reversal_add N
  map_smul' := HistorySourceNaturality.reversal_smul N
  norm_map' := reversal_norm N

@[simp] theorem sectorReversal_apply (N : ℕ) (x : SectorSpace N) :
    sectorReversal N x = reversal N x := rfl

@[simp] theorem sectorReversal_square (N : ℕ) (x : SectorSpace N) :
    sectorReversal N (sectorReversal N x) = -x :=
  HistorySourceNaturality.reversal_square N x

@[simp] theorem sectorReversal_symm (N : ℕ) (x : SectorSpace N) :
    (sectorReversal N).symm x = -sectorReversal N x := rfl

/-- Agreement with the source antiunitary is tested at every actual label. -/
theorem haar_intertwines (N : ℕ) (x : SectorSpace N) (h : HistoryLabel N) :
    HistoryHaarResponse.sectorUnitary N (sectorReversal N x) h =
      Geometry.SourceReversalIsometry.sourceReversal
        (HistoryHaarResponse.sectorUnitary N x h) := by
  apply Geometry.SourceScalarResponse.spinCoordinates.injective
  rw [Geometry.SourceReversalIsometry.sourceReversal_apply,
    Geometry.SourceScalarResponse.spinCoordinates_reversal]
  simp only [HistoryHaarResponse.sectorUnitary_apply,
    Geometry.SourceScalarResponse.spinCoordinates, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem sectorAction_intertwines (N : ℕ) (M : Mat2)
    (hM : ReversalRealConnector.ReversalReal M) (x : SectorSpace N) :
    sectorAction N M (sectorReversal N x) = sectorReversal N (sectorAction N M x) := by
  simpa only [HistorySourceNaturality.operator_spinLift, sectorReversal_apply] using
    (HistorySourceNaturality.spinLift_reversalCompatible_iff N M).mpr hM x

/-- Both source sectors retain their complete arithmetic label sets. -/
def pairReversal (N : ℕ) : WithLp 2 (SectorSpace N × SectorSpace N) →
    WithLp 2 (SectorSpace N × SectorSpace N) :=
  fun x => WithLp.toLp 2 (sectorReversal N (WithLp.ofLp x).1,
    sectorReversal N (WithLp.ofLp x).2)

theorem pairReversal_add (N : ℕ) (x y : WithLp 2 (SectorSpace N × SectorSpace N)) :
    pairReversal N (x + y) = pairReversal N x + pairReversal N y := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> exact map_add (sectorReversal N) _ _

theorem pairReversal_smul (N : ℕ) (c : ℂ)
    (x : WithLp 2 (SectorSpace N × SectorSpace N)) :
    pairReversal N (c • x) = star c • pairReversal N x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> exact HistorySourceNaturality.reversal_smul N c _

theorem pairReversal_inner (N : ℕ) (x y : WithLp 2 (SectorSpace N × SectorSpace N)) :
    inner ℂ (pairReversal N x) (pairReversal N y) = inner ℂ y x := by
  simp only [WithLp.prod_inner_apply, pairReversal,
    sectorReversal_apply, reversal_inner]

theorem pairReversal_square (N : ℕ) (x : WithLp 2 (SectorSpace N × SectorSpace N)) :
    pairReversal N (pairReversal N x) = -x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> exact sectorReversal_square N _

def fullReversal (N : ℕ) (x : Space N) : Space N :=
  (HistoryCliffordAction.sectorCoordinates N).symm
    (pairReversal N (HistoryCliffordAction.sectorCoordinates N x))

@[simp] theorem fullReversal_coordinates (N : ℕ) (x : Space N) :
    HistoryCliffordAction.sectorCoordinates N (fullReversal N x) =
      pairReversal N (HistoryCliffordAction.sectorCoordinates N x) :=
  (HistoryCliffordAction.sectorCoordinates N).apply_symm_apply _

theorem fullReversal_add (N : ℕ) (x y : Space N) :
    fullReversal N (x + y) = fullReversal N x + fullReversal N y := by
  simp only [fullReversal, map_add, pairReversal_add]

theorem fullReversal_smul (N : ℕ) (c : ℂ) (x : Space N) :
    fullReversal N (c • x) = star c • fullReversal N x := by
  simp only [fullReversal, map_smul, pairReversal_smul]

theorem fullReversal_inner (N : ℕ) (x y : Space N) :
    inner ℂ (fullReversal N x) (fullReversal N y) = inner ℂ y x := by
  simp only [fullReversal, LinearIsometryEquiv.inner_map_map, pairReversal_inner]

theorem fullReversal_square (N : ℕ) (x : Space N) :
    fullReversal N (fullReversal N x) = -x := by
  apply (HistoryCliffordAction.sectorCoordinates N).injective
  simp only [fullReversal_coordinates, pairReversal_square, map_neg]

theorem fullReversal_norm (N : ℕ) (x : Space N) : ‖fullReversal N x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (fullReversal N x),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) x, fullReversal_inner]

theorem fullReversal_neg (N : ℕ) (x : Space N) : fullReversal N (-x) = -fullReversal N x :=
  map_neg (AddMonoidHom.mk' (fullReversal N) (fullReversal_add N)) x

/-- The original coordinate formula, separately on both source sectors. -/
theorem fullReversal_apply (N : ℕ) (x : Space N) (h : HistoryLabel N) :
    (∀ i : Fin 2, fullReversal N x (h, Sum.inl i) =
      ReversalRealConnector.reversal (fun j => x (h, Sum.inl j)) i) ∧
    (∀ i : Fin 2, fullReversal N x (h, Sum.inr i) =
      ReversalRealConnector.reversal (fun j => x (h, Sum.inr j)) i) := by
  constructor <;> intro i <;> rfl

/-- Real arithmetic weights commute with this antiunitary; complex weights
are conjugated. This includes the actual central sign and Gaussian weights. -/
theorem real_weight_intertwines (N : ℕ) (c : HistoryLabel N → ℝ) (x : Space N) :
    fullReversal N (action N (historyLift N (Matrix.diagonal fun h => (c h : ℂ))) x) =
      action N (historyLift N (Matrix.diagonal fun h => (c h : ℂ))) (fullReversal N x) := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  cases i with
  | inl i =>
    rw [(fullReversal_apply N _ h).1, action_apply]
    fin_cases i <;> simp [historyLift, Fintype.sum_prod_type, Matrix.one_apply,
      Matrix.diagonal, ReversalRealConnector.reversal, fullReversal_apply, mul_comm]
  | inr i =>
    rw [(fullReversal_apply N _ h).2, action_apply]
    fin_cases i <;> simp [historyLift, Fintype.sum_prod_type, Matrix.one_apply,
      Matrix.diagonal, ReversalRealConnector.reversal, fullReversal_apply, mul_comm]

theorem gaussian_intertwines (N : ℕ) (t : ℝ) (x : Space N) :
    fullReversal N (action N (gaussian N t) x) =
      action N (gaussian N t) (fullReversal N x) :=
  real_weight_intertwines N (fun h => Real.exp (-t * ((h.1.val + 1 : ℕ) : ℝ) ^ 2)) x

theorem occupation_intertwines (N : ℕ) (x : Space N) :
    fullReversal N (action N (occupationGrading N) x) =
      action N (occupationGrading N) (fullReversal N x) := by
  have he : occupationGrading N = historyLift N (Matrix.diagonal fun h =>
      (((-1 : ℝ) ^ GeneratedPrimeParity.rootPrimeCount (h.1.val + 1)) : ℂ)) := by
    unfold occupationGrading
    congr 1
    ext h k
    simp [HistoryCentralSectors.sign]
  rw [he]
  simpa only [Complex.ofReal_pow] using real_weight_intertwines N
    (fun h : HistoryLabel N => (-1 : ℝ) ^
      GeneratedPrimeParity.rootPrimeCount (h.1.val + 1)) x

def fullAntiunitary (N : ℕ) : Space N ≃ₗᵢ⋆[ℂ] Space N where
  toFun := fullReversal N
  invFun x := -fullReversal N x
  left_inv x := by
    change -fullReversal N (fullReversal N x) = x
    rw [fullReversal_square, neg_neg]
  right_inv x := by
    change fullReversal N (-fullReversal N x) = x
    rw [fullReversal_neg, fullReversal_square, neg_neg]
  map_add' := fullReversal_add N
  map_smul' := fullReversal_smul N
  norm_map' := fullReversal_norm N

/-- Every coefficient of the antiunitary is fixed by the original source
formula. The comparison class contains all antiunitaries of this carrier. -/
theorem fullAntiunitary_unique (N : ℕ) (J : Space N ≃ₗᵢ⋆[ℂ] Space N)
    (hJ : ∀ x, sectorCoordinates N (J x) = pairReversal N (sectorCoordinates N x)) :
    J = fullAntiunitary N := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (sectorCoordinates N).injective
  exact (hJ x).trans (fullReversal_coordinates N x).symm

/-- The two actual source frames preserve the full antiunitary independently. -/
theorem frame_intertwines (N : ℕ) (g : HistoryElementaryConnector.Frame) (x : Space N) :
    action N (HistoryElementaryConnector.frame N g) (fullReversal N x) =
      fullReversal N (action N (HistoryElementaryConnector.frame N g) x) := by
  apply (HistoryCliffordAction.sectorCoordinates N).injective
  rw [fullReversal_coordinates]
  apply WithLp.ofLp_injective 2
  rw [show HistoryElementaryConnector.frame N g =
    HistoryEvenResponse.matrix N ((g.1 : Mat2), (g.2 : Mat2)) from rfl]
  rw [HistoryEvenResponse.sectorCoordinates_matrix]
  simp only [pairReversal, WithLp.ofLp_toLp]
  rw [HistoryEvenResponse.sectorCoordinates_matrix]
  apply Prod.ext
  · exact sectorAction_intertwines N _
      (Geometry.SourceScalarResponse.specialUnitary_reversalReal g.1) _
  · exact sectorAction_intertwines N _
      (Geometry.SourceScalarResponse.specialUnitary_reversalReal g.2) _

/-- Reversal of the source does not discard the adjoint connector block. -/
theorem connector_intertwines (N : ℕ) (v : HistoryElementaryConnector.Spinor) (x : Space N) :
    action N (HistoryElementaryConnector.scalarConnector N v) (fullReversal N x) =
      fullReversal N (action N (HistoryElementaryConnector.scalarConnector N v) x) := by
  apply (HistoryCliffordAction.sectorCoordinates N).injective
  rw [fullReversal_coordinates]
  apply WithLp.ofLp_injective 2
  rw [show HistoryElementaryConnector.scalarConnector N v =
    connector N (ReversalRealConnector.connectorOfDoublet v) from rfl]
  rw [HistoryComplexConnector.sectorCoordinates_connector]
  simp only [pairReversal, WithLp.ofLp_toLp]
  rw [HistoryComplexConnector.sectorCoordinates_connector]
  apply Prod.ext
  · exact sectorAction_intertwines N _ (ReversalRealConnector.connectorOfDoublet_reversalReal v) _
  · exact sectorAction_intertwines N _ (SourceReversalRealConnector.reversalReal_adjoint
      (ReversalRealConnector.connectorOfDoublet_reversalReal v)) _

structure Conclusions : Prop where
  complete_sector_metric : ∀ N (x y : SectorSpace N),
    inner ℂ (sectorReversal N x) (sectorReversal N y) = inner ℂ y x
  complete_source_metric : ∀ N (x y : Space N),
    inner ℂ (fullAntiunitary N x) (fullAntiunitary N y) = inner ℂ y x
  square_minus_identity : ∀ N (x : Space N), fullAntiunitary N (fullAntiunitary N x) = -x
  actual_haar_transport : ∀ N (x : SectorSpace N) (h : HistoryLabel N),
    HistoryHaarResponse.sectorUnitary N (sectorReversal N x) h =
      Geometry.SourceReversalIsometry.sourceReversal (HistoryHaarResponse.sectorUnitary N x h)
  independent_source_frames : ∀ N g (x : Space N),
    action N (HistoryElementaryConnector.frame N g) (fullReversal N x) =
      fullReversal N (action N (HistoryElementaryConnector.frame N g) x)
  complete_connector : ∀ N v (x : Space N),
    action N (HistoryElementaryConnector.scalarConnector N v) (fullReversal N x) =
      fullReversal N (action N (HistoryElementaryConnector.scalarConnector N v) x)
  gaussian_compatibility : ∀ N t (x : Space N),
    fullReversal N (action N (gaussian N t) x) = action N (gaussian N t) (fullReversal N x)
  occupation_compatibility : ∀ N (x : Space N),
    fullReversal N (action N (occupationGrading N) x) =
      action N (occupationGrading N) (fullReversal N x)

theorem generated : Conclusions where
  complete_sector_metric := reversal_inner
  complete_source_metric := fullReversal_inner
  square_minus_identity := fullReversal_square
  actual_haar_transport := haar_intertwines
  independent_source_frames := frame_intertwines
  complete_connector := connector_intertwines
  gaussian_compatibility := gaussian_intertwines
  occupation_compatibility := occupation_intertwines

end GeneratedFoundations.Arithmetic.HistoryReversalIsometry
