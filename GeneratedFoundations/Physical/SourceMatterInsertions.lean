module

public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Physical.SourceGaugeUnitary
public import GeneratedFoundations.Operations.FermionInsertions

/-!
# Insertions on the exterior completion of the generated matter fibre

The one-matter space and its inner product are the existing complete
sixteen-dimensional source carrier, including the neutral line. In its
fermionic exterior completion, insertion is exterior multiplication and
removal is contraction with the same source inner product. Their mixed
relation therefore has no separately supplied normalization.

The exterior completion is the fermionic completion used by the field
realization. These statements construct its finite insertion algebra and
the lift of the existing source action; they do not identify a source
resolution parameter with event time or select an interacting vacuum.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceMatterInsertions

open SourceChiralCarrier GeneratedFoundations.Operations

set_option maxRecDepth 4096

abbrev Matter := FullMatter
abbrev Coordinates := EuclideanSpace ℂ FullIndex
abbrev Fock := FermionInsertions.Fock Coordinates
abbrev vacuum : Fock := FermionInsertions.vacuum

/-- The original source isometry supplies the insertion coordinates. -/
def create (v : Matter) (x : Fock) : Fock :=
  FermionInsertions.create (fullCoordinates v) x

def remove (v : Matter) : Fock →ₗ[ℂ] Fock :=
  FermionInsertions.remove (fullCoordinates v)

def coordinateOperator (A : Matter →ₗ[ℂ] Matter) : Coordinates →ₗ[ℂ] Coordinates :=
  fullCoordinates.toLinearMap.comp (A.comp fullCoordinates.symm.toLinearMap)

theorem coordinateOperator_apply (A : Matter →ₗ[ℂ] Matter) (v : Matter) :
    coordinateOperator A (fullCoordinates v) = fullCoordinates (A v) := by
  simp [coordinateOperator]

def transport (U : Matter →ₗ[ℂ] Matter) : Fock →ₐ[ℂ] Fock :=
  ExteriorAlgebra.map (coordinateOperator U)

theorem transport_create (U : Matter →ₗ[ℂ] Matter) (v : Matter) (x : Fock) :
    transport U (create v x) = create (U v) (transport U x) := by
  simp only [transport, create, FermionInsertions.create, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateOperator_apply]

theorem mixed_car (v w : Matter) (x : Fock) :
    remove v (create w x) + create w (remove v x) = inner ℂ v w • x := by
  simpa only [create, remove, fullCoordinates.inner_map_map] using
    FermionInsertions.mixed_car (fullCoordinates v) (fullCoordinates w) x

theorem vacuum_pair (v w : Matter) :
    remove v (create w vacuum) = algebraMap ℂ Fock (inner ℂ v w) := by
  simpa only [create, remove, fullCoordinates.inner_map_map] using
    FermionInsertions.vacuum_pair (fullCoordinates v) (fullCoordinates w)

/-- The original effective gauge group acts on the same insertion algebra. -/
def gaugeTransport (g : SourceGaugeUnitary.EffectiveGroup) : Fock →ₐ[ℂ] Fock :=
  transport (SourceGaugeUnitary.effectiveLinearAction g).toLinearMap

theorem gaugeTransport_create (g : SourceGaugeUnitary.EffectiveGroup)
    (v : Matter) (x : Fock) :
    gaugeTransport g (create v x) =
      create (SourceGaugeUnitary.effectiveLinearAction g v) (gaugeTransport g x) :=
  transport_create _ _ _

/-- All original finite source currents use the same, uniquely lifted insertion action. -/
def sourceCurrent (A : Matter →ₗ[ℂ] Matter) : Fock →ₗ[ℂ] Fock :=
  FermionInsertions.oneBody (EuclideanSpace.basisFun FullIndex ℂ) (coordinateOperator A)

theorem sourceCurrent_create (A : Matter →ₗ[ℂ] Matter) (v : Matter) (x : Fock) :
    sourceCurrent A (create v x) = create (A v) x + create v (sourceCurrent A x) := by
  unfold sourceCurrent create
  rw [FermionInsertions.oneBody_create, coordinateOperator_apply]

theorem sourceCurrent_vacuum (A : Matter →ₗ[ℂ] Matter) :
    sourceCurrent A vacuum = 0 :=
  FermionInsertions.oneBody_vacuum _ _

theorem sourceCurrent_unique (A : Matter →ₗ[ℂ] Matter) (K : Fock →ₗ[ℂ] Fock)
    (hv : K vacuum = 0)
    (hi : ∀ v x, K (create v x) = create (A v) x + create v (K x)) :
    K = sourceCurrent A := by
  apply FermionInsertions.oneBody_unique _ _ _ hv
  intro v x
  obtain ⟨w, rfl⟩ := fullCoordinates.surjective v
  rw [coordinateOperator_apply]
  exact hi w x

theorem sourceCurrent_mul (A : Matter →ₗ[ℂ] Matter) (x y : Fock) :
    sourceCurrent A (x * y) = sourceCurrent A x * y + x * sourceCurrent A y :=
  FermionInsertions.oneBody_mul _ _ _ _

/-- The source action and ordinary product determine the extension, including its unit value. -/
theorem sourceCurrent_unique_derivation (A : Matter →ₗ[ℂ] Matter)
    (K : Fock →ₗ[ℂ] Fock)
    (hprod : ∀ x y, K (x * y) = K x * y + x * K y)
    (hsource : ∀ v, K (create v vacuum) = create (A v) vacuum) :
    K = sourceCurrent A := by
  apply FermionInsertions.oneBody_unique_derivation _ _ _ hprod
  intro v
  obtain ⟨w, rfl⟩ := fullCoordinates.surjective v
  rw [coordinateOperator_apply]
  simpa only [create, FermionInsertions.create, vacuum,
    FermionInsertions.vacuum, mul_one] using hsource w

/-- Both chiral source copies occur in the insertion algebra. -/
theorem chiral_cross_pair (v w : SourceMinimalRepresentation.SourceCarrier) :
    remove (leftInclusion v) (create (rightInclusion w) vacuum) = 0 := by
  rw [vacuum_pair, left_right_inner, map_zero]

theorem full_basis_pair (i j : FullIndex) :
    remove (fullBasis i) (create (fullBasis j) vacuum) =
      algebraMap ℂ Fock (if i = j then 1 else 0) := by
  rw [vacuum_pair]
  congr 1
  exact fullBasis.inner_eq_ite i j

/-- Insertions and the induced source action on the existing complete fibre. -/
structure Conclusions : Prop where
  complete_fibre : Module.finrank ℂ Matter = 16
  normalized_product : ∀ v w x,
    remove v (create w x) + create w (remove v x) = inner ℂ v w • x
  basis_pair : ∀ i j,
    remove (fullBasis i) (create (fullBasis j) vacuum) =
      algebraMap ℂ Fock (if i = j then 1 else 0)
  source_action : ∀ (A : Matter →ₗ[ℂ] Matter) v x,
    sourceCurrent A (create v x) = create (A v) x + create v (sourceCurrent A x)
  source_product : ∀ (A : Matter →ₗ[ℂ] Matter) x y,
    sourceCurrent A (x * y) = sourceCurrent A x * y + x * sourceCurrent A y
  source_extension_unique : ∀ (A : Matter →ₗ[ℂ] Matter) (K : Fock →ₗ[ℂ] Fock),
    (∀ x y, K (x * y) = K x * y + x * K y) →
    (∀ v, K (create v vacuum) = create (A v) vacuum) →
    K = sourceCurrent A
  common_frame : ∀ g v x,
    gaugeTransport g (create v x) =
      create (SourceGaugeUnitary.effectiveLinearAction g v) (gaugeTransport g x)

theorem generated : Conclusions where
  complete_fibre := fullMatter_finrank
  normalized_product := mixed_car
  basis_pair := full_basis_pair
  source_action := sourceCurrent_create
  source_product := sourceCurrent_mul
  source_extension_unique := sourceCurrent_unique_derivation
  common_frame := gaugeTransport_create

end GeneratedFoundations.Physical.SourceMatterInsertions
