module

public import GeneratedFoundations.Arithmetic.HistoryEvenResponse
public import GeneratedFoundations.Geometry.SourceSpinIdentification
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Gaussian--Haar transport of complete arithmetic source responses

Each actual history--phase label retains the two original Gaussian source
coordinates in each source sector. The common polynomial map sends those
coordinates into the degree-one Haar carrier without changing their metric.
Applying that map at every label gives a unitary equivalence of the complete
arithmetic carrier. No history or phase is selected or averaged out.

All matrix responses are conjugated by that same equivalence, including
cross-label and cross-sector entries. The even and odd source operators are
then calculated in the Haar representation. These are representations of the
already constructed arithmetic objects, with their internally derived number
of copies; no physical colour or matter multiplicity enters the construction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarResponse

open HistoryCliffordAction
open HistoryComplexConnector (Mat2 sectorAction connector)
open Geometry.SourceSpinIdentification

abbrev HaarSector (N : ℕ) := PiLp 2 (fun _ : HistoryLabel N => S)
abbrev HaarSpace (N : ℕ) := WithLp 2 (HaarSector N × HaarSector N)

/-- The original ordered polynomial map is applied at every actual label.
The reindexing and currying maps are the explicit product coordinates. -/
def sectorUnitary (N : ℕ) : SectorSpace N ≃ₗᵢ[ℂ] HaarSector N :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.sigmaEquivProd (HistoryLabel N) (Fin 2)).symm).trans
      ((LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : HistoryLabel N) (_ : Fin 2) => ℂ)).trans
          (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => coordinateUnitary)))

def sectorEquiv (N : ℕ) : SectorSpace N ≃ₗ[ℂ] HaarSector N :=
  (sectorUnitary N).toLinearEquiv

@[simp] theorem sectorEquiv_apply (N : ℕ) (x : SectorSpace N) (h : HistoryLabel N) :
    sectorEquiv N x h =
      coordinateUnitary (WithLp.toLp 2 (fun i => x (h, i))) := rfl

theorem sectorEquiv_inner (N : ℕ) (x y : SectorSpace N) :
    inner ℂ (sectorEquiv N x) (sectorEquiv N y) = inner ℂ x y := by
  simp only [PiLp.inner_apply, sectorEquiv_apply, coordinateUnitary_apply,
    coordinateEquiv_inner, RCLike.inner_apply']
  rw [Fintype.sum_prod_type]

@[simp] theorem sectorUnitary_apply (N : ℕ) (x : SectorSpace N) (h : HistoryLabel N) :
    sectorUnitary N x h =
      coordinateUnitary (WithLp.toLp 2 (fun i => x (h, i))) := rfl

def fullUnitary (N : ℕ) : Space N ≃ₗᵢ[ℂ] HaarSpace N :=
  (sectorCoordinates N).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (sectorUnitary N) (sectorUnitary N))

@[simp] theorem fullUnitary_positive (N : ℕ) (x : Space N) :
    (WithLp.ofLp (fullUnitary N x)).1 =
      sectorUnitary N (WithLp.ofLp (sectorCoordinates N x)).1 := rfl

@[simp] theorem fullUnitary_negative (N : ℕ) (x : Space N) :
    (WithLp.ofLp (fullUnitary N x)).2 =
      sectorUnitary N (WithLp.ofLp (sectorCoordinates N x)).2 := rfl

/-- The complete inner product is preserved before any response is selected. -/
theorem fullUnitary_inner (N : ℕ) (x y : Space N) :
    inner ℂ (fullUnitary N x) (fullUnitary N y) = inner ℂ x y := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (sectorEquiv N (WithLp.ofLp (sectorCoordinates N x)).1)
      (sectorEquiv N (WithLp.ofLp (sectorCoordinates N y)).1) +
    inner ℂ (sectorEquiv N (WithLp.ofLp (sectorCoordinates N x)).2)
      (sectorEquiv N (WithLp.ofLp (sectorCoordinates N y)).2) = _
  rw [sectorEquiv_inner, sectorEquiv_inner, ← WithLp.prod_inner_apply]
  exact (sectorCoordinates N).inner_map_map x y

/-- Complete matrix conjugation, including all cross-label coefficients. -/
def fullAction (N : ℕ) : Algebra N ≃ₐ[ℂ] Module.End ℂ (HaarSpace N) :=
  (action N).trans ((fullUnitary N).toLinearEquiv.conjAlgEquiv ℂ)

theorem fullAction_intertwines (N : ℕ) (A : Algebra N) (x : Space N) :
    fullAction N A (fullUnitary N x) = fullUnitary N (action N A x) := by
  change fullUnitary N (action N A ((fullUnitary N).symm (fullUnitary N x))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem fullAction_faithful (N : ℕ) : Function.Injective (fullAction N) :=
  (fullAction N).injective

set_option maxHeartbeats 800000 in
theorem fullAction_adjoint (N : ℕ) (A : Algebra N) :
    fullAction N A.conjTranspose = (fullAction N A).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (fullUnitary N (action N A.conjTranspose ((fullUnitary N).symm x))) y =
    inner ℂ x (fullUnitary N (action N A ((fullUnitary N).symm y)))
  have hx := fullUnitary_inner N (action N A.conjTranspose ((fullUnitary N).symm x))
    ((fullUnitary N).symm y)
  have hy := fullUnitary_inner N ((fullUnitary N).symm x)
    (action N A ((fullUnitary N).symm y))
  rw [LinearIsometryEquiv.apply_symm_apply] at hx hy
  rw [hx, hy, ← action_adjoint, LinearMap.adjoint_inner_left]

theorem complete_response_invariant (N : ℕ) (A : Algebra N) (x y : Space N) :
    inner ℂ (fullUnitary N x) (fullAction N A (fullUnitary N y)) =
      inner ℂ x (action N A y) := by
  rw [fullAction_intertwines]
  exact fullUnitary_inner N x (action N A y)

/-- The same source matrix acts pointwise, without suppressing any label. -/
def sectorResponse (N : ℕ) (M : Mat2) : Module.End ℂ (HaarSector N) where
  toFun x := WithLp.toLp 2 (fun h => spinAction M (x h))
  map_add' x y := by
    apply PiLp.ext
    intro h
    exact map_add (spinAction M) (x h) (y h)
  map_smul' c x := by
    apply PiLp.ext
    intro h
    exact map_smul (spinAction M) c (x h)

theorem sectorUnitary_intertwines (N : ℕ) (M : Mat2) (x : SectorSpace N) :
    sectorUnitary N (sectorAction N M x) = sectorResponse N M (sectorUnitary N x) := by
  apply PiLp.ext
  intro h
  exact (spinAction_coordinates M (WithLp.toLp 2 (fun i => x (h, i)))).symm

theorem fullUnitary_even (N : ℕ) (p : Mat2 × Mat2) (x : Space N) :
    WithLp.ofLp (fullUnitary N (action N (HistoryEvenResponse.matrix N p) x)) =
      (sectorResponse N p.1 (WithLp.ofLp (fullUnitary N x)).1,
        sectorResponse N p.2 (WithLp.ofLp (fullUnitary N x)).2) := by
  have h := HistoryEvenResponse.sectorCoordinates_matrix N p x
  apply Prod.ext
  · change sectorUnitary N (WithLp.ofLp (sectorCoordinates N
        (action N (HistoryEvenResponse.matrix N p) x))).1 = _
    rw [congrArg Prod.fst h]
    exact sectorUnitary_intertwines N _ _
  · change sectorUnitary N (WithLp.ofLp (sectorCoordinates N
        (action N (HistoryEvenResponse.matrix N p) x))).2 = _
    rw [congrArg Prod.snd h]
    exact sectorUnitary_intertwines N _ _

theorem fullUnitary_connector (N : ℕ) (M : Mat2) (x : Space N) :
    WithLp.ofLp (fullUnitary N (action N (connector N M) x)) =
      (sectorResponse N M (WithLp.ofLp (fullUnitary N x)).2,
        sectorResponse N M.conjTranspose (WithLp.ofLp (fullUnitary N x)).1) := by
  have h := HistoryComplexConnector.sectorCoordinates_connector N M x
  apply Prod.ext
  · change sectorUnitary N (WithLp.ofLp (sectorCoordinates N
        (action N (connector N M) x))).1 = _
    rw [congrArg Prod.fst h]
    exact sectorUnitary_intertwines N _ _
  · change sectorUnitary N (WithLp.ofLp (sectorCoordinates N
        (action N (connector N M) x))).2 = _
    rw [congrArg Prod.snd h]
    exact sectorUnitary_intertwines N _ _

theorem haar_dimension (N : ℕ) :
    Module.finrank ℂ (HaarSpace N) = 4 * Fintype.card (HistoryLabel N) := by
  rw [← (fullUnitary N).toLinearEquiv.finrank_eq, space_finrank]

structure Conclusions : Prop where
  derived_dimension : ∀ N,
    Module.finrank ℂ (HaarSpace N) = 4 * Fintype.card (HistoryLabel N)
  faithful_response : ∀ N, Function.Injective (fullAction N)
  adjoint_transport : ∀ N A,
    fullAction N A.conjTranspose = (fullAction N A).adjoint
  all_cross_terms : ∀ N A (x y : Space N),
    inner ℂ (fullUnitary N x) (fullAction N A (fullUnitary N y)) =
      inner ℂ x (action N A y)
  odd_response : ∀ N M (x : Space N),
    WithLp.ofLp (fullUnitary N (action N (connector N M) x)) =
      (sectorResponse N M (WithLp.ofLp (fullUnitary N x)).2,
        sectorResponse N M.conjTranspose (WithLp.ofLp (fullUnitary N x)).1)

theorem generated : Conclusions where
  derived_dimension := haar_dimension
  faithful_response := fullAction_faithful
  adjoint_transport := fullAction_adjoint
  all_cross_terms := complete_response_invariant
  odd_response := fullUnitary_connector

end GeneratedFoundations.Arithmetic.HistoryHaarResponse
