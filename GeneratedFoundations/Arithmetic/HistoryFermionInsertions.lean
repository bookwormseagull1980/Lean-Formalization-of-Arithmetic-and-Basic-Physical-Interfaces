module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames
public import GeneratedFoundations.Operations.FermionInsertions

/-!
# Exterior insertions on the complete arithmetic source carrier

The carrier is the existing history--phase space with both original source
sectors. Its orthonormal basis and its source-frame action determine the
insertion normalization. Every original history label remains present.
The extension of any one-body response is the unique derivation with that
response on one-particle insertions. The same exterior transport preserves
the contact identity before and after any common linear preparation.

The arithmetic carrier dimension is computed from its actual labels;
no physical matter dimension or gauge charge is used.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryFermionInsertions

open GeneratedFoundations.Operations
open HistoryCliffordAction (Space Index HistoryLabel SectorSpace basis action)
open HistoryComplexConnector (positiveInclusion negativeInclusion)

abbrev Fock (N : ℕ) := FermionInsertions.Fock (Space N)

def vacuum (N : ℕ) : Fock N := FermionInsertions.vacuum

def create (N : ℕ) (v : Space N) (x : Fock N) : Fock N :=
  FermionInsertions.create v x

def remove (N : ℕ) (v : Space N) : Fock N →ₗ[ℂ] Fock N :=
  FermionInsertions.remove v

theorem complete_fibre (N : ℕ) :
    Module.finrank ℂ (Space N) = 4 * Fintype.card (HistoryLabel N) :=
  HistoryCliffordAction.space_finrank N

theorem mixed_car (N : ℕ) (v w : Space N) (x : Fock N) :
    remove N v (create N w x) + create N w (remove N v x) = inner ℂ v w • x :=
  FermionInsertions.mixed_car v w x

theorem vacuum_pair (N : ℕ) (v w : Space N) :
    remove N v (create N w (vacuum N)) = algebraMap ℂ (Fock N) (inner ℂ v w) :=
  FermionInsertions.vacuum_pair v w

theorem chiral_cross_pair (N : ℕ) (v w : SectorSpace N) :
    remove N (positiveInclusion N v) (create N (negativeInclusion N w) (vacuum N)) = 0 := by
  rw [vacuum_pair, HistoryComplexConnector.inclusions_orthogonal, map_zero]

theorem full_basis_pair (N : ℕ) (i j : Index N) :
    remove N (basis N i) (create N (basis N j) (vacuum N)) =
      algebraMap ℂ (Fock N) (if i = j then 1 else 0) := by
  rw [vacuum_pair, (basis N).inner_eq_ite]

def transport (N : ℕ) (U : Space N →ₗ[ℂ] Space N) : Fock N →ₐ[ℂ] Fock N :=
  FermionInsertions.transport U

theorem transport_create (N : ℕ) (U : Space N →ₗ[ℂ] Space N)
    (v : Space N) (x : Fock N) :
    transport N U (create N v x) = create N (U v) (transport N U x) :=
  FermionInsertions.transport_create U v x

theorem transport_identity (N : ℕ) (x : Fock N) :
    transport N LinearMap.id x = x := by
  exact congrArg (fun F : Fock N →ₐ[ℂ] Fock N => F x) ExteriorAlgebra.map_id

theorem transport_comp (N : ℕ) (U V : Space N →ₗ[ℂ] Space N) (x : Fock N) :
    transport N U (transport N V x) = transport N (U.comp V) x :=
  FermionInsertions.transport_comp U V x

theorem transport_unique (N : ℕ) (U : Space N →ₗ[ℂ] Space N)
    (F : Fock N →ₐ[ℂ] Fock N)
    (h : ∀ v, F (create N v (vacuum N)) = create N (U v) (vacuum N)) :
    F = transport N U := by
  apply FermionInsertions.transport_unique U F
  intro v
  simpa only [create, vacuum, FermionInsertions.create, FermionInsertions.vacuum,
    mul_one] using h v

def sourceCurrent (N : ℕ) (A : Space N →ₗ[ℂ] Space N) : Fock N →ₗ[ℂ] Fock N :=
  FermionInsertions.oneBody (basis N) A

theorem sourceCurrent_create (N : ℕ) (A : Space N →ₗ[ℂ] Space N)
    (v : Space N) (x : Fock N) :
    sourceCurrent N A (create N v x) =
      create N (A v) x + create N v (sourceCurrent N A x) :=
  FermionInsertions.oneBody_create (basis N) A v x

theorem sourceCurrent_vacuum (N : ℕ) (A : Space N →ₗ[ℂ] Space N) :
    sourceCurrent N A (vacuum N) = 0 :=
  FermionInsertions.oneBody_vacuum (basis N) A

theorem sourceCurrent_mul (N : ℕ) (A : Space N →ₗ[ℂ] Space N) (x y : Fock N) :
    sourceCurrent N A (x * y) = sourceCurrent N A x * y + x * sourceCurrent N A y :=
  FermionInsertions.oneBody_mul (basis N) A x y

theorem sourceCurrent_unique (N : ℕ) (A : Space N →ₗ[ℂ] Space N)
    (K : Fock N →ₗ[ℂ] Fock N) (hv : K (vacuum N) = 0)
    (hi : ∀ v x, K (create N v x) = create N (A v) x + create N v (K x)) :
    K = sourceCurrent N A :=
  FermionInsertions.oneBody_unique (basis N) A K hv hi

theorem sourceCurrent_unique_derivation (N : ℕ) (A : Space N →ₗ[ℂ] Space N)
    (K : Fock N →ₗ[ℂ] Fock N)
    (hprod : ∀ x y, K (x * y) = K x * y + x * K y)
    (hsource : ∀ v, K (create N v (vacuum N)) = create N (A v) (vacuum N)) :
    K = sourceCurrent N A := by
  apply FermionInsertions.oneBody_unique_derivation (basis N) A K hprod
  intro v
  simpa only [create, vacuum, FermionInsertions.create, FermionInsertions.vacuum,
    mul_one] using hsource v

/-- The previously constructed source frames act on this same exterior algebra. -/
def frameTransport (N : ℕ) (g : HistoryElementaryConnector.Frame) : Fock N →ₐ[ℂ] Fock N :=
  transport N (HistoryEffectiveFrames.stateResponse N g)

theorem frameTransport_create (N : ℕ) (g : HistoryElementaryConnector.Frame)
    (v : Space N) (x : Fock N) :
    frameTransport N g (create N v x) =
      create N (HistoryEffectiveFrames.stateResponse N g v) (frameTransport N g x) :=
  transport_create N _ v x

def removalInsertion (N : ℕ) (before middle after : Space N →ₗ[ℂ] Space N)
    (v w : Space N) (x : Fock N) : Fock N :=
  transport N after (remove N v (transport N middle (create N w (transport N before x))))

def insertionRemoval (N : ℕ) (before middle after : Space N →ₗ[ℂ] Space N)
    (v w : Space N) (x : Fock N) : Fock N :=
  transport N after (create N w (transport N middle (remove N v (transport N before x))))

theorem coincident_pair (N : ℕ) (before after : Space N →ₗ[ℂ] Space N)
    (v w : Space N) (x : Fock N) :
    removalInsertion N before LinearMap.id after v w x +
      insertionRemoval N before LinearMap.id after v w x =
      inner ℂ v w • transport N after (transport N before x) := by
  simp only [removalInsertion, insertionRemoval, transport_identity]
  rw [← map_add, mixed_car]
  exact (transport N after).toLinearMap.map_smul _ _

theorem prepared_coincident_pair (N : ℕ) (before after : Space N →ₗ[ℂ] Space N)
    (v w : Space N) (x : Fock N) (preparation : Fock N →ₗ[ℂ] ℂ) :
    preparation (removalInsertion N before LinearMap.id after v w x) +
      preparation (insertionRemoval N before LinearMap.id after v w x) =
      inner ℂ v w * preparation (transport N after (transport N before x)) := by
  rw [← map_add, coincident_pair, map_smul]
  rfl

structure Conclusions : Prop where
  actual_dimension : ∀ N,
    Module.finrank ℂ (Space N) = 4 * Fintype.card (HistoryLabel N)
  normalized_product : ∀ N v w x,
    remove N v (create N w x) + create N w (remove N v x) = inner ℂ v w • x
  source_product : ∀ N (A : Space N →ₗ[ℂ] Space N) x y,
    sourceCurrent N A (x * y) = sourceCurrent N A x * y + x * sourceCurrent N A y
  unique_source_extension : ∀ N (A : Space N →ₗ[ℂ] Space N) (K : Fock N →ₗ[ℂ] Fock N),
    (∀ x y, K (x * y) = K x * y + x * K y) →
    (∀ v, K (create N v (vacuum N)) = create N (A v) (vacuum N)) →
    K = sourceCurrent N A
  same_source_frame : ∀ N g v x,
    frameTransport N g (create N v x) =
      create N (HistoryEffectiveFrames.stateResponse N g v) (frameTransport N g x)
  common_contact : ∀ N (before after : Space N →ₗ[ℂ] Space N) v w x,
    removalInsertion N before LinearMap.id after v w x +
      insertionRemoval N before LinearMap.id after v w x =
      inner ℂ v w • transport N after (transport N before x)

theorem generated : Conclusions where
  actual_dimension := complete_fibre
  normalized_product := mixed_car
  source_product := sourceCurrent_mul
  unique_source_extension := sourceCurrent_unique_derivation
  same_source_frame := frameTransport_create
  common_contact := coincident_pair

end GeneratedFoundations.Arithmetic.HistoryFermionInsertions
