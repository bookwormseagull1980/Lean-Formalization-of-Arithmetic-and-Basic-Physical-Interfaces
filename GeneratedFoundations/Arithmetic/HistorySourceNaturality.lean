module

public import GeneratedFoundations.Arithmetic.HistoryHaarResponse
public import GeneratedFoundations.Operations.ColourNaturalConnector

/-!
# Natural source responses on complete history--phase fibres

The first factor contains every actual history and finite phase up to the
observation cutoff. An arbitrary matrix on this factor tensored with the
two-mode source is allowed as input. Commutation with the complete history
matrix algebra forces a single, uniquely determined source response, identical
at every label. This factorization is proved, not assumed in the input type.

Finite coordinates use a bijection of the actual label set; no label is
discarded and its cardinality is not prescribed by the physical branch.
The resulting response agrees with the already constructed Gaussian action
and its Haar transport.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistorySourceNaturality

open HistoryCliffordAction (HistoryLabel SectorSpace historyPoint)
open HistoryComplexConnector (Mat2 sectorAction)
open GeneratedFoundations.Operations

abbrev HistoryMatrix (N : ℕ) := Matrix (HistoryLabel N) (HistoryLabel N) ℂ
abbrev Index (N : ℕ) := HistoryLabel N × Fin 2
abbrev SourceMatrix (N : ℕ) := Matrix (Index N) (Index N) ℂ

local instance (N : ℕ) : DecidableEq (HistoryLabel N) := Classical.decEq _
local instance (N : ℕ) : NeZero (Fintype.card (HistoryLabel N)) :=
  ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨historyPoint N⟩)⟩

def labelCoordinates (N : ℕ) : HistoryLabel N ≃ Fin (Fintype.card (HistoryLabel N)) :=
  Fintype.equivFin _

def historyCoordinates (N : ℕ) :
    HistoryMatrix N ≃ₐ[ℂ] ColourNaturalConnector.ColourMatrix (Fintype.card (HistoryLabel N)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (labelCoordinates N)

def coordinates (N : ℕ) :
    SourceMatrix N ≃ₐ[ℂ] ColourNaturalConnector.Connector (Fintype.card (HistoryLabel N)) :=
  Matrix.reindexAlgEquiv ℂ ℂ
    (Equiv.prodCongr (labelCoordinates N) (Equiv.refl (Fin 2)))

def historyAction (N : ℕ) (A : HistoryMatrix N) : SourceMatrix N := A ⊗ₖ (1 : Mat2)

def spinLift (N : ℕ) (M : Mat2) : SourceMatrix N := (1 : HistoryMatrix N) ⊗ₖ M

/-- A common invertible change of the complete history coordinates cancels
between the two legs of a source response. No history entry is discarded. -/
theorem history_change_cancels (N : ℕ) (g : (HistoryMatrix N)ˣ) (M : Mat2) :
    historyAction N (g : HistoryMatrix N) * spinLift N M *
      historyAction N (g⁻¹ : (HistoryMatrix N)ˣ) = spinLift N M := by
  simp only [historyAction, spinLift]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [mul_one, one_mul, Units.mul_inv]

theorem history_spin_frame_cancels (N : ℕ) (g : (HistoryMatrix N)ˣ)
    (L M R : Mat2) :
    ((g : HistoryMatrix N) ⊗ₖ L) * spinLift N M *
      (((g⁻¹ : (HistoryMatrix N)ˣ) : HistoryMatrix N) ⊗ₖ R) =
        spinLift N (L * M * R) := by
  simp only [spinLift]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [mul_one, Units.mul_inv]

def Natural (N : ℕ) (T : SourceMatrix N) : Prop :=
  ∀ A : HistoryMatrix N, T * historyAction N A = historyAction N A * T

theorem coordinates_historyAction (N : ℕ) (A : HistoryMatrix N) :
    coordinates N (historyAction N A) =
      ColourNaturalConnector.colourAction (historyCoordinates N A) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

theorem coordinates_spinLift (N : ℕ) (M : Mat2) :
    coordinates N (spinLift N M) =
      ColourNaturalConnector.spinLift (Fintype.card (HistoryLabel N)) M := by
  ext ⟨a, i⟩ ⟨b, j⟩
  change (if (labelCoordinates N).symm a = (labelCoordinates N).symm b then 1 else 0) *
      M i j = (if a = b then 1 else 0) * M i j
  simp only [(labelCoordinates N).symm.injective.eq_iff]

theorem natural_iff_coordinates (N : ℕ) (T : SourceMatrix N) :
    Natural N T ↔ ColourNaturalConnector.Natural (coordinates N T) := by
  constructor
  · intro hT A
    obtain ⟨B, rfl⟩ := (historyCoordinates N).surjective A
    have h := congrArg (coordinates N) (hT B)
    simpa only [map_mul, coordinates_historyAction] using h
  · intro hT A
    apply (coordinates N).injective
    simpa only [map_mul, coordinates_historyAction] using hT (historyCoordinates N A)

theorem spinLift_injective (N : ℕ) : Function.Injective (spinLift N) := by
  intro M K h
  apply ColourNaturalConnector.spinLift_injective (Fintype.card (HistoryLabel N))
  simpa only [coordinates_spinLift] using congrArg (coordinates N) h

theorem spinLift_natural (N : ℕ) (M : Mat2) : Natural N (spinLift N M) := by
  apply (natural_iff_coordinates N _).mpr
  rw [coordinates_spinLift]
  exact ColourNaturalConnector.spinLift_natural _ _

/-- Every matrix satisfying actual history naturality has a unique source factor. -/
theorem natural_iff_existsUnique_source (N : ℕ) (T : SourceMatrix N) :
    Natural N T ↔ ∃! M : Mat2, T = spinLift N M := by
  constructor
  · intro hT
    obtain ⟨M, hM, _⟩ :=
      (ColourNaturalConnector.natural_iff_existsUnique_spinor (coordinates N T)).mp
        ((natural_iff_coordinates N T).mp hT)
    have he : T = spinLift N M := by
      apply (coordinates N).injective
      rw [coordinates_spinLift]
      exact hM
    refine ⟨M, he, ?_⟩
    intro K hK
    exact spinLift_injective N (hK.symm.trans he)
  · rintro ⟨M, rfl, _⟩
    exact spinLift_natural N M

/-- The same coefficient algebra acts on the complete Gaussian sector. -/
def operator (N : ℕ) : SourceMatrix N ≃ₐ[ℂ] Module.End ℂ (SectorSpace N) :=
  Matrix.toLinAlgEquiv'.trans
    ((WithLp.linearEquiv 2 ℂ (Index N → ℂ)).symm.conjAlgEquiv ℂ)

theorem operator_spinLift (N : ℕ) (M : Mat2) :
    operator N (spinLift N M) = sectorAction N M := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨h, i⟩
  change (∑ j, spinLift N M (h, i) j * x j) = ∑ j, M i j * x (h, j)
  simp [spinLift, Fintype.sum_prod_type, Matrix.one_apply,
    ite_mul]

theorem natural_operator_iff (N : ℕ) (T : SourceMatrix N) :
    Natural N T ↔ ∃! M : Mat2, operator N T = sectorAction N M := by
  rw [natural_iff_existsUnique_source]
  constructor
  · rintro ⟨M, hM, hu⟩
    refine ⟨M, ?_, ?_⟩
    · rw [hM, operator_spinLift]
    · intro K hK
      apply hu
      apply (operator N).injective
      simpa only [operator_spinLift] using hK
  · rintro ⟨M, hM, hu⟩
    refine ⟨M, ?_, ?_⟩
    · apply (operator N).injective
      simpa only [operator_spinLift] using hM
    · intro K hK
      apply hu
      rw [hK, operator_spinLift]

theorem haar_source_intertwines (N : ℕ) (M : Mat2) (x : SectorSpace N) :
    HistoryHaarResponse.sectorUnitary N (operator N (spinLift N M) x) =
      HistoryHaarResponse.sectorResponse N M (HistoryHaarResponse.sectorUnitary N x) := by
  rw [operator_spinLift]
  exact HistoryHaarResponse.sectorUnitary_intertwines N M x

/-- The original source reversal acts at each actual arithmetic label. It does
not permute history labels or change their occupation parity. -/
def reversal (N : ℕ) (x : SectorSpace N) : SectorSpace N :=
  WithLp.toLp 2 (fun p => ReversalRealConnector.reversal (fun i => x (p.1, i)) p.2)

theorem reversal_square (N : ℕ) (x : SectorSpace N) :
    reversal N (reversal N x) = -x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  exact congrFun (ReversalRealConnector.reversal_square (fun j => x (h, j))) i

theorem reversal_smul (N : ℕ) (c : ℂ) (x : SectorSpace N) :
    reversal N (c • x) = star c • reversal N x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  exact congrFun (ReversalRealConnector.reversal_smul c (fun j => x (h, j))) i

def ReversalCompatible (N : ℕ) (T : SourceMatrix N) : Prop :=
  ∀ x : SectorSpace N, operator N T (reversal N x) = reversal N (operator N T x)

theorem spinLift_reversalCompatible_iff (N : ℕ) (M : Mat2) :
    ReversalCompatible N (spinLift N M) ↔ ReversalRealConnector.ReversalReal M := by
  simp only [ReversalCompatible, operator_spinLift]
  constructor
  · intro h v
    ext i
    have hi := congrArg (fun x : SectorSpace N => x (historyPoint N, i))
      (h (WithLp.toLp 2 (fun p => v p.2)))
    exact hi
  · intro h x
    apply PiLp.ext
    rintro ⟨a, i⟩
    exact congrFun (h (fun j => x (a, j))) i

/-- Both conditions are tested on an arbitrary full matrix. Their unique
doublet is a computed coordinate of the original source reversal equation. -/
theorem natural_reversal_iff_unique_doublet (N : ℕ) (T : SourceMatrix N) :
    Natural N T ∧ ReversalCompatible N T ↔
      ∃! v : ReversalRealConnector.Spinor,
        T = spinLift N (ReversalRealConnector.connectorOfDoublet v) := by
  constructor
  · rintro ⟨hn, hr⟩
    obtain ⟨M, hT, _⟩ := (natural_iff_existsUnique_source N T).mp hn
    have hM := (spinLift_reversalCompatible_iff N M).mp (hT ▸ hr)
    obtain ⟨v, hv, _⟩ := (ReversalRealConnector.reversalReal_iff_existsUnique_doublet M).mp hM
    have he := hT.trans (congrArg (spinLift N) hv)
    refine ⟨v, he, ?_⟩
    intro w hw
    apply ReversalRealConnector.connectorOfDoublet_injective
    exact spinLift_injective N (hw.symm.trans he)
  · rintro ⟨v, rfl, _⟩
    exact ⟨spinLift_natural N _,
      (spinLift_reversalCompatible_iff N _).mpr
        (ReversalRealConnector.connectorOfDoublet_reversalReal v)⟩

theorem natural_reversal_iff_unique_quaternion (N : ℕ) (T : SourceMatrix N) :
    Natural N T ∧ ReversalCompatible N T ↔
      ∃! q : Quaternion ℝ, T = spinLift N (Geometry.SourceQuaternionAmplitude.matrixMap q) := by
  constructor
  · rintro ⟨hn, hr⟩
    obtain ⟨M, hT, _⟩ := (natural_iff_existsUnique_source N T).mp hn
    have hM := (spinLift_reversalCompatible_iff N M).mp (hT ▸ hr)
    obtain ⟨q, hq, _⟩ := (SourceReversalRealConnector.reversalReal_iff_unique_sourceAmplitude M).mp hM
    have he := hT.trans (congrArg (spinLift N) hq.symm)
    refine ⟨q, he, ?_⟩
    intro p hp
    apply Geometry.SourceQuaternionAmplitude.matrixMap_injective
    exact spinLift_injective N (hp.symm.trans he)
  · rintro ⟨q, rfl, _⟩
    exact ⟨spinLift_natural N _,
      (spinLift_reversalCompatible_iff N _).mpr
        (SourceReversalRealConnector.matrixMap_reversalReal q)⟩

def doubletResponse (N : ℕ) : ReversalRealConnector.Spinor →ₗ[ℝ] SourceMatrix N where
  toFun v := spinLift N (ReversalRealConnector.connectorOfDoublet v)
  map_add' v w := by
    rw [ReversalRealConnector.connectorOfDoublet_add]
    exact Matrix.kronecker_add _ _ _
  map_smul' c v := by
    rw [ReversalRealConnector.connectorOfDoublet_real_smul]
    exact Matrix.kronecker_smul c _ _

theorem doubletResponse_injective (N : ℕ) : Function.Injective (doubletResponse N) :=
  (spinLift_injective N).comp ReversalRealConnector.connectorOfDoublet_injective

def elementarySpace (N : ℕ) : Submodule ℝ (SourceMatrix N) := (doubletResponse N).range

theorem canonical_elementary (N : ℕ) (v : ReversalRealConnector.Spinor) :
    Natural N (doubletResponse N v) ∧ ReversalCompatible N (doubletResponse N v) :=
  ⟨spinLift_natural N _, (spinLift_reversalCompatible_iff N _).mpr
    (ReversalRealConnector.connectorOfDoublet_reversalReal v)⟩

theorem mem_elementarySpace_iff (N : ℕ) (T : SourceMatrix N) :
    T ∈ elementarySpace N ↔ Natural N T ∧ ReversalCompatible N T := by
  constructor
  · rintro ⟨v, hv⟩
    exact hv ▸ canonical_elementary N v
  · intro hT
    obtain ⟨v, hv, _⟩ := (natural_reversal_iff_unique_doublet N T).mp hT
    exact ⟨v, hv.symm⟩

theorem elementarySpace_finrank (N : ℕ) :
    Module.finrank ℝ (elementarySpace N) = 4 := by
  change Module.finrank ℝ (doubletResponse N).range = 4
  rw [← (LinearEquiv.ofInjective (doubletResponse N) (doubletResponse_injective N)).finrank_eq]
  change Module.finrank ℝ (Fin 2 → ℂ) = 4
  simp [Module.finrank_pi_fintype]

structure Conclusions : Prop where
  arbitrary_input : ∀ N T, Natural N T ↔ ∃! M, T = spinLift N M
  faithful_source : ∀ N, Function.Injective (spinLift N)
  actual_operator : ∀ N M, operator N (spinLift N M) = sectorAction N M
  haar_transport : ∀ N M (x : SectorSpace N),
    HistoryHaarResponse.sectorUnitary N (operator N (spinLift N M) x) =
      HistoryHaarResponse.sectorResponse N M (HistoryHaarResponse.sectorUnitary N x)
  unique_real_source : ∀ N T,
    Natural N T ∧ ReversalCompatible N T ↔
      ∃! q : Quaternion ℝ, T = spinLift N (Geometry.SourceQuaternionAmplitude.matrixMap q)
  elementary_dimension : ∀ N, Module.finrank ℝ (elementarySpace N) = 4
  complete_history_cancellation : ∀ N (g : (HistoryMatrix N)ˣ) M,
    historyAction N (g : HistoryMatrix N) * spinLift N M *
      historyAction N (g⁻¹ : (HistoryMatrix N)ˣ) = spinLift N M
  complete_frame_cancellation : ∀ N (g : (HistoryMatrix N)ˣ) L M R,
    ((g : HistoryMatrix N) ⊗ₖ L) * spinLift N M *
      (((g⁻¹ : (HistoryMatrix N)ˣ) : HistoryMatrix N) ⊗ₖ R) =
        spinLift N (L * M * R)

theorem generated : Conclusions where
  arbitrary_input := natural_iff_existsUnique_source
  faithful_source := spinLift_injective
  actual_operator := operator_spinLift
  haar_transport := haar_source_intertwines
  unique_real_source := natural_reversal_iff_unique_quaternion
  elementary_dimension := elementarySpace_finrank
  complete_history_cancellation := history_change_cancels
  complete_frame_cancellation := history_spin_frame_cancels

end GeneratedFoundations.Arithmetic.HistorySourceNaturality
