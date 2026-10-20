module

public import GeneratedFoundations.Arithmetic.HistoryModuleRepresentation
public import GeneratedFoundations.Operations.MatrixBlockRepresentations
public import Mathlib.Algebra.Algebra.Pi

/-!
# Root-preserving sectors of the complete generated history carrier

At cutoff `N`, the roots are exactly `1,...,N+1`; each sector retains every
history and every phase of its own root. The root-preserving operation algebra
is the product of the full matrix algebras of those fibres. The matrix labels
below are finite coordinates of these actual fibres, with an explicit algebra
equivalence and a unitary transport to the native coefficient space.

The common matrix-unit classification derives the multiplicities of arbitrary
faithful realizations. The least dimension is the sum of the actual sector
cardinalities, and every least adjoint-compatible realization is unitarily
equivalent to the constructed one. The selected algebra preserves roots;
this does not identify it with the algebra of all cross-root operations.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryRootSectors

open Operations.MatrixBlockRepresentations

abbrev Roots (N : ℕ) := Fin (N + 1)

def size (N : ℕ) (b : Roots N) : ℕ := Fintype.card (HistoryModuleRepresentation.Index b.val)

theorem size_pos (N : ℕ) (b : Roots N) : 0 < size N b :=
  Fintype.card_pos_iff.mpr ⟨HistoryModuleRepresentation.base b.val⟩

def base (N : ℕ) (b : Roots N) : Fin (size N b) := ⟨0, size_pos N b⟩

abbrev Algebra (N : ℕ) := BlockAlgebra (K := ℂ) (size N)
abbrev Space (N : ℕ) := StandardHilbert (size N)
abbrev NativeAlgebra (N : ℕ) := ∀ b : Roots N, HistoryModuleRepresentation.Algebra b.val
abbrev NativeSpace (N : ℕ) := PiLp 2 fun b : Roots N => HistoryModuleRepresentation.Space b.val

def indexCoordinates (n : ℕ) : HistoryModuleRepresentation.Index n ≃
    Fin (Fintype.card (HistoryModuleRepresentation.Index n)) := Fintype.equivFin _

def algebraCoordinates (N : ℕ) : NativeAlgebra N ≃ₐ[ℂ] Algebra N :=
  AlgEquiv.piCongrRight fun b => Matrix.reindexAlgEquiv ℂ ℂ (indexCoordinates b.val)

def nativeAdjoint {N : ℕ} (A : NativeAlgebra N) : NativeAlgebra N :=
  fun b => (A b).conjTranspose

theorem algebraCoordinates_adjoint (N : ℕ) (A : NativeAlgebra N) :
    algebraCoordinates N (nativeAdjoint A) = blockAdjoint (size N) (algebraCoordinates N A) := by
  ext b i j
  rfl

def coordinateRepresentation {H : Type*} [AddCommGroup H] [Module ℂ H]
    (N : ℕ) (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) :
    Algebra N →ₐ[ℂ] Module.End ℂ H := ρ.comp (algebraCoordinates N).symm.toAlgHom

def nativeOfCoordinate {H : Type*} [AddCommGroup H] [Module ℂ H]
    (N : ℕ) (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) :
    NativeAlgebra N →ₐ[ℂ] Module.End ℂ H := ρ.comp (algebraCoordinates N).toAlgHom

theorem coordinateRepresentation_nativeOfCoordinate
    {H : Type*} [AddCommGroup H] [Module ℂ H] (N : ℕ)
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) :
    coordinateRepresentation N (nativeOfCoordinate N ρ) = ρ := by
  ext A x
  simp [coordinateRepresentation, nativeOfCoordinate]

theorem nativeOfCoordinate_coordinateRepresentation
    {H : Type*} [AddCommGroup H] [Module ℂ H] (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) :
    nativeOfCoordinate N (coordinateRepresentation N ρ) = ρ := by
  ext A x
  simp [coordinateRepresentation, nativeOfCoordinate]

theorem nativeOfCoordinate_injective
    {H : Type*} [AddCommGroup H] [Module ℂ H] (N : ℕ)
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    Function.Injective (nativeOfCoordinate N ρ) :=
  hρ.comp (algebraCoordinates N).injective

def carrierCoordinates (N : ℕ) : NativeSpace N ≃ₗᵢ[ℂ] Space N :=
  LinearIsometryEquiv.piLpCongrRight 2 fun b =>
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (indexCoordinates b.val)

def representation (N : ℕ) : Algebra N →ₐ[ℂ] Module.End ℂ (Space N) :=
  standardHilbertRepresentation (size N)

def nativeRepresentation (N : ℕ) : NativeAlgebra N →ₐ[ℂ] Module.End ℂ (NativeSpace N) :=
  (((carrierCoordinates N).symm.toLinearEquiv.conjAlgEquiv ℂ).toAlgHom).comp
    ((representation N).comp (algebraCoordinates N).toAlgHom)

theorem native_intertwining (N : ℕ) (A : NativeAlgebra N) (x : NativeSpace N) :
    carrierCoordinates N (nativeRepresentation N A x) =
      representation N (algebraCoordinates N A) (carrierCoordinates N x) :=
  (carrierCoordinates N).apply_symm_apply _

theorem native_inner_preserved (N : ℕ) (x y : NativeSpace N) :
    inner ℂ (carrierCoordinates N x) (carrierCoordinates N y) = inner ℂ x y :=
  (carrierCoordinates N).inner_map_map x y

theorem representation_injective (N : ℕ) : Function.Injective (representation N) :=
  standardHilbertRepresentation_injective (size N)

theorem nativeRepresentation_injective (N : ℕ) : Function.Injective (nativeRepresentation N) :=
  ((carrierCoordinates N).symm.toLinearEquiv.conjAlgEquiv ℂ).injective.comp
    ((representation_injective N).comp (algebraCoordinates N).injective)

theorem representation_starCompatible (N : ℕ) : StarCompatible (size N) (representation N) :=
  standardHilbertRepresentation_starCompatible (size N)

def NativeStarCompatible {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) : Prop :=
  ∀ A x y, inner ℂ (ρ A x) y = inner ℂ x (ρ (nativeAdjoint A) y)

theorem nativeOfCoordinate_starCompatible
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (N : ℕ)
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) (hρ : StarCompatible (size N) ρ) :
    NativeStarCompatible N (nativeOfCoordinate N ρ) := by
  intro A x y
  simpa only [nativeOfCoordinate, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    algebraCoordinates_adjoint] using hρ (algebraCoordinates N A) x y

theorem algebraCoordinates_symm_adjoint (N : ℕ) (A : Algebra N) :
    nativeAdjoint ((algebraCoordinates N).symm A) =
      (algebraCoordinates N).symm (blockAdjoint (size N) A) := by
  apply (algebraCoordinates N).injective
  rw [algebraCoordinates_adjoint, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

theorem coordinateRepresentation_starCompatible
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : NativeStarCompatible N ρ) :
    StarCompatible (size N) (coordinateRepresentation N ρ) := by
  intro A x y
  simpa only [coordinateRepresentation, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    algebraCoordinates_symm_adjoint] using hρ ((algebraCoordinates N).symm A) x y

theorem nativeRepresentation_starCompatible (N : ℕ) :
    NativeStarCompatible N (nativeRepresentation N) := by
  intro A x y
  calc
    inner ℂ (nativeRepresentation N A x) y =
        inner ℂ (carrierCoordinates N (nativeRepresentation N A x))
          (carrierCoordinates N y) := (native_inner_preserved N _ _).symm
    _ = inner ℂ (carrierCoordinates N x)
        (carrierCoordinates N (nativeRepresentation N (nativeAdjoint A) y)) := by
      rw [native_intertwining, native_intertwining, algebraCoordinates_adjoint]
      exact representation_starCompatible N _ _ _
    _ = inner ℂ x (nativeRepresentation N (nativeAdjoint A) y) :=
      native_inner_preserved N _ _

/-- Identity on one actual root fibre and zero on every other retained root. -/
def nativeSectorIdentity (N : ℕ) (b : Roots N) : NativeAlgebra N := Pi.single b 1

theorem nativeSectorIdentity_adjoint (N : ℕ) (b : Roots N) :
    nativeAdjoint (nativeSectorIdentity N b) = nativeSectorIdentity N b := by
  funext c
  by_cases h : b = c
  · subst c
    simp [nativeAdjoint, nativeSectorIdentity]
  · simp [nativeAdjoint, nativeSectorIdentity, h]

theorem nativeSectorIdentity_sq (N : ℕ) (b : Roots N) :
    nativeSectorIdentity N b * nativeSectorIdentity N b = nativeSectorIdentity N b := by
  funext c
  by_cases h : b = c
  · subst c
    simp [nativeSectorIdentity]
  · simp [nativeSectorIdentity, h]

theorem nativeSectorIdentity_mul_ne (N : ℕ) (b c : Roots N) (hbc : b ≠ c) :
    nativeSectorIdentity N b * nativeSectorIdentity N c = 0 := by
  funext d
  by_cases h : b = d
  · subst d
    simp [nativeSectorIdentity, Ne.symm hbc]
  · simp [nativeSectorIdentity, h]

theorem sum_nativeSectorIdentity (N : ℕ) : (∑ b, nativeSectorIdentity N b) = 1 := by
  funext c
  simp [nativeSectorIdentity]

def sectorProjection (N : ℕ) (b : Roots N) : Module.End ℂ (NativeSpace N) :=
  nativeRepresentation N (nativeSectorIdentity N b)

theorem sectorProjection_sq (N : ℕ) (b : Roots N) :
    sectorProjection N b * sectorProjection N b = sectorProjection N b := by
  change nativeRepresentation N (nativeSectorIdentity N b) *
    nativeRepresentation N (nativeSectorIdentity N b) = nativeRepresentation N (nativeSectorIdentity N b)
  rw [← map_mul, nativeSectorIdentity_sq]

theorem sectorProjection_mul_ne (N : ℕ) (b c : Roots N) (hbc : b ≠ c) :
    sectorProjection N b * sectorProjection N c = 0 := by
  change nativeRepresentation N (nativeSectorIdentity N b) *
    nativeRepresentation N (nativeSectorIdentity N c) = 0
  rw [← map_mul, nativeSectorIdentity_mul_ne N b c hbc, map_zero]

theorem sum_sectorProjection (N : ℕ) : (∑ b, sectorProjection N b) = 1 := by
  simpa only [sectorProjection, map_sum, map_one] using
    congrArg (nativeRepresentation N) (sum_nativeSectorIdentity N)

theorem sector_reconstruction (N : ℕ) (x : NativeSpace N) :
    (∑ b, sectorProjection N b x) = x := by
  have h := congrArg (fun F : Module.End ℂ (NativeSpace N) => F x) (sum_sectorProjection N)
  simpa using h

theorem sectorProjection_inner (N : ℕ) (b : Roots N) (x y : NativeSpace N) :
    inner ℂ (sectorProjection N b x) y = inner ℂ x (sectorProjection N b y) := by
  simpa only [sectorProjection, nativeSectorIdentity_adjoint] using
    nativeRepresentation_starCompatible N (nativeSectorIdentity N b) x y

theorem sector_orthogonal (N : ℕ) (b c : Roots N) (hbc : b ≠ c)
    (x y : NativeSpace N) :
    inner ℂ (sectorProjection N b x) (sectorProjection N c y) = 0 := by
  rw [sectorProjection_inner]
  have h : sectorProjection N b (sectorProjection N c y) = 0 := by
    change (sectorProjection N b * sectorProjection N c) y = 0
    rw [sectorProjection_mul_ne N b c hbc]
    rfl
  rw [h]
  simp

theorem space_dimension (N : ℕ) : Module.finrank ℂ (Space N) = ∑ b, size N b :=
  standardHilbertRepresentation_finrank (size N)

theorem native_space_dimension (N : ℕ) :
    Module.finrank ℂ (NativeSpace N) =
      ∑ b : Roots N, Fintype.card (CompleteHistory.History (b.val + 1)) * (b.val + 1) := by
  rw [(carrierCoordinates N).toLinearEquiv.finrank_eq, space_dimension]
  apply Finset.sum_congr rfl
  intro b _
  exact CompleteNaturalObject.completeFiber_card (b.val + 1)

section Comparison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

theorem faithful_dimension_lowerBound (N : ℕ)
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    (∑ b, size N b) ≤ Module.finrank ℂ H :=
  faithful_finrank_lowerBound (size N) ρ hρ (base N)

theorem multiplicity_dimension (N : ℕ) (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) :
    Module.finrank ℂ H = ∑ b, size N b *
      Module.finrank ℂ (multiplicitySpace (size N) ρ (base N) b) :=
  finrank_eq_sum_multiplicities (size N) ρ (base N)

theorem native_least_dimension (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    Module.finrank ℂ (NativeSpace N) ≤ Module.finrank ℂ H := by
  rw [(carrierCoordinates N).toLinearEquiv.finrank_eq, space_dimension]
  exact faithful_dimension_lowerBound N (coordinateRepresentation N ρ)
    (hρ.comp (algebraCoordinates N).symm.injective)

def NativeLeast (N : ℕ) (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) : Prop :=
  Function.Injective ρ ∧ NativeStarCompatible N ρ ∧
    Module.finrank ℂ H = Module.finrank ℂ (NativeSpace N)

def CoordinateLeast (N : ℕ) (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) : Prop :=
  Function.Injective ρ ∧ StarCompatible (size N) ρ ∧ Module.finrank ℂ H = ∑ b, size N b

theorem nativeRepresentation_isLeast (N : ℕ) : NativeLeast N (nativeRepresentation N) :=
  ⟨nativeRepresentation_injective N, nativeRepresentation_starCompatible N, rfl⟩

/-- The dimension criterion is equivalent to the universal least-dimension
property for realizations of the actual native operation algebra. -/
theorem native_least_iff (N : ℕ) (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) :
    NativeLeast N ρ ↔ Function.Injective ρ ∧ NativeStarCompatible N ρ ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        [FiniteDimensional ℂ E] (σ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ E),
          Function.Injective σ → Module.finrank ℂ H ≤ Module.finrank ℂ E) := by
  constructor
  · rintro ⟨hρ, hstar, hdim⟩
    refine ⟨hρ, hstar, ?_⟩
    intro E _ _ _ σ hσ
    rw [hdim]
    exact native_least_dimension N σ hσ
  · rintro ⟨hρ, hstar, hleast⟩
    refine ⟨hρ, hstar, Nat.le_antisymm ?_ (native_least_dimension N ρ hρ)⟩
    exact hleast (NativeSpace N) (nativeRepresentation N) (nativeRepresentation_injective N)

omit [FiniteDimensional ℂ H] in
theorem least_iff_coordinates (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) :
    NativeLeast N ρ ↔ CoordinateLeast N (coordinateRepresentation N ρ) := by
  have hdim : Module.finrank ℂ (NativeSpace N) = ∑ b, size N b := by
    rw [(carrierCoordinates N).toLinearEquiv.finrank_eq, space_dimension]
  constructor
  · rintro ⟨hρ, hstar, hmin⟩
    exact ⟨hρ.comp (algebraCoordinates N).symm.injective,
      coordinateRepresentation_starCompatible N ρ hstar, hmin.trans hdim⟩
  · rintro ⟨hρ, hstar, hmin⟩
    have hi := nativeOfCoordinate_injective N (coordinateRepresentation N ρ) hρ
    have hs := nativeOfCoordinate_starCompatible N (coordinateRepresentation N ρ) hstar
    rw [nativeOfCoordinate_coordinateRepresentation] at hi hs
    exact ⟨hi, hs, hmin.trans hdim.symm⟩

theorem least_iff_multiplicity_one (N : ℕ)
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    Module.finrank ℂ H = ∑ b, size N b ↔
      ∀ b, Module.finrank ℂ (multiplicitySpace (size N) ρ (base N) b) = 1 :=
  minimal_finrank_iff_multiplicities_one (size N) ρ hρ (base N)

theorem least_unitarilyEquivalent (N : ℕ) (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H)
    (hρ : Function.Injective ρ) (hstar : StarCompatible (size N) ρ)
    (hdim : Module.finrank ℂ H = ∑ b, size N b) :
    ∃ U : H ≃ₗᵢ[ℂ] Space N, ∀ A x, U (ρ A x) = representation N A (U x) :=
  minimalFaithfulJointRep_unique (size N) ρ hstar hρ (representation N)
    (representation_starCompatible N) (representation_injective N) (base N)
    hdim (space_dimension N)

/-- Least realizations of the actual native algebra return to the actual
history coefficient carrier, not merely to an abstract coordinate space. -/
theorem native_least_unitarilyEquivalent (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : NativeLeast N ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] NativeSpace N,
      ∀ A x, U (ρ A x) = nativeRepresentation N A (U x) := by
  obtain ⟨U, hU⟩ := least_unitarilyEquivalent N (coordinateRepresentation N ρ)
    ((least_iff_coordinates N ρ).mp hρ).1
    ((least_iff_coordinates N ρ).mp hρ).2.1
    ((least_iff_coordinates N ρ).mp hρ).2.2
  refine ⟨U.trans (carrierCoordinates N).symm, ?_⟩
  intro A x
  apply (carrierCoordinates N).injective
  simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    native_intertwining, coordinateRepresentation, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    hU (algebraCoordinates N A) x

end Comparison

structure Conclusions : Prop where
  faithful : ∀ N, Function.Injective (nativeRepresentation N)
  adjoint_compatible : ∀ N, NativeStarCompatible N (nativeRepresentation N)
  constructed_least : ∀ N, NativeLeast N (nativeRepresentation N)
  full_coordinates : ∀ N, Nonempty (NativeAlgebra N ≃ₐ[ℂ] Algebra N)
  unitary_coordinates : ∀ N, Nonempty (NativeSpace N ≃ₗᵢ[ℂ] Space N)
  actual_transport : ∀ (N : ℕ) (A : NativeAlgebra N) (x : NativeSpace N),
    carrierCoordinates N (nativeRepresentation N A x) =
      representation N (algebraCoordinates N A) (carrierCoordinates N x)
  actual_dimension : ∀ N, Module.finrank ℂ (NativeSpace N) =
    ∑ b : Roots N, Fintype.card (CompleteHistory.History (b.val + 1)) * (b.val + 1)
  root_reconstruction : ∀ (N : ℕ) (x : NativeSpace N), (∑ b, sectorProjection N b x) = x
  root_orthogonality : ∀ (N : ℕ) (b c : Roots N), b ≠ c →
    ∀ x y : NativeSpace N, inner ℂ (sectorProjection N b x) (sectorProjection N c y) = 0
  minimal_classification : ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Algebra N →ₐ[ℂ] Module.End ℂ H), Function.Injective ρ →
      StarCompatible (size N) ρ → Module.finrank ℂ H = ∑ b, size N b →
        ∃ U : H ≃ₗᵢ[ℂ] Space N, ∀ A x, U (ρ A x) = representation N A (U x)
  native_classification : ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H), NativeLeast N ρ →
      ∃ U : H ≃ₗᵢ[ℂ] NativeSpace N,
        ∀ A x, U (ρ A x) = nativeRepresentation N A (U x)

theorem generated : Conclusions where
  faithful := nativeRepresentation_injective
  adjoint_compatible := nativeRepresentation_starCompatible
  constructed_least := nativeRepresentation_isLeast
  full_coordinates := fun N => ⟨algebraCoordinates N⟩
  unitary_coordinates := fun N => ⟨carrierCoordinates N⟩
  actual_transport := native_intertwining
  actual_dimension := native_space_dimension
  root_reconstruction := sector_reconstruction
  root_orthogonality := sector_orthogonal
  minimal_classification := fun N _ _ _ _ ρ => least_unitarilyEquivalent N ρ
  native_classification := fun N _ _ _ _ ρ => native_least_unitarilyEquivalent N ρ

end GeneratedFoundations.Arithmetic.HistoryRootSectors
