module

public import GeneratedFoundations.Arithmetic.HistoryMatrixAlgebra
public import GeneratedFoundations.Operations.MatrixModuleClassification

/-!
# Least faithful Hilbert realization of the complete history--phase algebra

The coefficient labels are the actual generated histories and their phase
kernels. The full matrix algebra acts on their Euclidean coefficient space.
Its matrix units determine the multiplicity space of every other unital
realization. Consequently the least dimension is the actual fibre cardinality,
not a dimension imported from the physical carrier. Adjoint-compatible least
realizations are unitarily equivalent, with all matrix entries intertwined.

The root entry constructs the canonical realization. Arbitrary realizations
occur only in its comparison theorems, never as inputs to that entry.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryModuleRepresentation

open Operations.MatrixModuleClassification

abbrev Index (n : ℕ) := HistoryMatrixAlgebra.Index n
abbrev Algebra (n : ℕ) := HistoryMatrixAlgebra.Algebra n
abbrev Space (n : ℕ) := EuclideanSpace ℂ (Index n)

noncomputable instance (n : ℕ) : DecidableEq (Index n) := Classical.decEq _

def base (n : ℕ) : Index n :=
  (Classical.choice (HistoryObservation.history_nonempty (n + 1) (by omega)), 0)

def coefficientCoordinates (n : ℕ) : HistoryMatrixAlgebra.Space n ≃ₗ[ℂ] Space n :=
  (WithLp.linearEquiv 2 ℂ (Index n → ℂ)).symm

def representation (n : ℕ) : Algebra n →ₐ[ℂ] Module.End ℂ (Space n) :=
  ((coefficientCoordinates n).conjAlgEquiv ℂ).toAlgHom.comp
    (HistoryMatrixAlgebra.representation n).toAlgHom

theorem representation_apply (n : ℕ) (A : Algebra n) (v : Space n) (i : Index n) :
    representation n A v i = ∑ j, A i j * v j := rfl

theorem representation_injective (n : ℕ) : Function.Injective (representation n) :=
  ((coefficientCoordinates n).conjAlgEquiv ℂ).injective.comp
    (HistoryMatrixAlgebra.faithful n)

theorem representation_starCompatible (n : ℕ) : StarCompatible (representation n) := by
  intro A x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', representation_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem space_finrank (n : ℕ) : Module.finrank ℂ (Space n) = Fintype.card (Index n) :=
  finrank_euclideanSpace

theorem actual_dimension (n : ℕ) :
    Module.finrank ℂ (Space n) = Fintype.card (CompleteHistory.History (n + 1)) * (n + 1) := by
  rw [space_finrank]
  exact CompleteNaturalObject.completeFiber_card (n + 1)

/-- A coefficient map natural for every actual full-matrix operation has no
    hidden action on history or phase labels: only a scalar remains. -/
theorem coefficient_commutant (n : ℕ)
    (T : Module.End ℂ (HistoryMatrixAlgebra.Space n)) :
    (∀ (A : Algebra n) v,
      T (HistoryMatrixAlgebra.representation n A v) =
        HistoryMatrixAlgebra.representation n A (T v)) ↔
      ∃! c : ℂ, ∀ v, T v = c • v := by
  constructor
  · intro hT
    have hnatural : IsNatural T := hT
    obtain ⟨h, hh, _⟩ := (natural_iff_existsUnique_reducedMap T (base n)).mp hnatural
    let c : ℂ := h 1
    have hlinear (z : ℂ) : h z = c * z := by
      have hz := h.map_smul z 1
      simpa [c, smul_eq_mul, mul_comm] using hz
    have hc (v : HistoryMatrixAlgebra.Space n) : T v = c • v := by
      ext i
      rw [hh, hlinear]
      rfl
    refine ⟨c, hc, ?_⟩
    intro d hd
    have he := congrFun ((hc (fun _ => 1)).symm.trans (hd (fun _ => 1))) (base n)
    simpa using he.symm
  · rintro ⟨c, hc, _⟩ A v
    rw [hc, hc, map_smul]

section Comparison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

theorem faithful_dimension_lowerBound (n : ℕ)
    (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    Fintype.card (Index n) ≤ Module.finrank ℂ H :=
  faithful_finrank_lowerBound ρ hρ (base n)

theorem multiplicity_dimension (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H) :
    Module.finrank ℂ H = Fintype.card (Index n) *
      Module.finrank ℂ (multiplicitySpace ρ (base n)) :=
  finrank_eq_card_mul_multiplicity ρ (base n)

/-- The comparison class consists of unital faithful adjoint-compatible
    realizations of this actual full algebra. -/
def IsLeast (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H) : Prop :=
  Function.Injective ρ ∧ StarCompatible ρ ∧
    Module.finrank ℂ H = Fintype.card (Index n)

theorem representation_isLeast (n : ℕ) : IsLeast n (representation n) :=
  ⟨representation_injective n, representation_starCompatible n, space_finrank n⟩

omit [FiniteDimensional ℂ H] in
theorem least_dimension (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeast n ρ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E] (σ : Algebra n →ₐ[ℂ] Module.End ℂ E),
        Function.Injective σ → Module.finrank ℂ H ≤ Module.finrank ℂ E := by
  intro E _ _ _ σ hσ
  rw [hρ.2.2]
  exact faithful_dimension_lowerBound n σ hσ

theorem least_iff (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H) :
    IsLeast n ρ ↔ Function.Injective ρ ∧ StarCompatible ρ ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        [FiniteDimensional ℂ E] (σ : Algebra n →ₐ[ℂ] Module.End ℂ E),
          Function.Injective σ → Module.finrank ℂ H ≤ Module.finrank ℂ E) := by
  constructor
  · intro hρ
    exact ⟨hρ.1, hρ.2.1, least_dimension n ρ hρ⟩
  · rintro ⟨hρ, hstar, hleast⟩
    refine ⟨hρ, hstar, Nat.le_antisymm ?_ (faithful_dimension_lowerBound n ρ hρ)⟩
    have h := hleast (Space n) (representation n) (representation_injective n)
    simpa only [space_finrank] using h

theorem least_multiplicity_one (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeast n ρ) : Module.finrank ℂ (multiplicitySpace ρ (base n)) = 1 :=
  (minimal_finrank_iff_multiplicity_one ρ (base n)).mp hρ.2.2

omit [FiniteDimensional ℂ H] in
theorem least_finrank (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeast n ρ) : Module.finrank ℂ H = Module.finrank ℂ (Space n) :=
  hρ.2.2.trans (space_finrank n).symm

theorem least_unitarilyEquivalent (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeast n ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] Space n, ∀ A x, U (ρ A x) = representation n A (U x) :=
  minimalFaithfulRepresentation_unique ρ hρ.2.1 (representation n)
    (representation_starCompatible n) (base n) hρ.2.2 (space_finrank n)

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

theorem least_unique (n : ℕ) (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeast n ρ) (σ : Algebra n →ₐ[ℂ] Module.End ℂ H')
    (hσ : IsLeast n σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ A x, U (ρ A x) = σ A (U x) :=
  minimalFaithfulRepresentation_unique ρ hρ.2.1 σ hσ.2.1 (base n) hρ.2.2 hσ.2.2

end Comparison

structure Conclusions : Prop where
  faithful : ∀ n, Function.Injective (representation n)
  adjoint_compatible : ∀ n, StarCompatible (representation n)
  constructed_least : ∀ n, IsLeast n (representation n)
  dimension : ∀ n, Module.finrank ℂ (Space n) =
    Fintype.card (CompleteHistory.History (n + 1)) * (n + 1)
  scalar_commutant : ∀ (n : ℕ) (T : Module.End ℂ (HistoryMatrixAlgebra.Space n)),
    (∀ (A : Algebra n) v, T (HistoryMatrixAlgebra.representation n A v) =
      HistoryMatrixAlgebra.representation n A (T v)) ↔
        ∃! c : ℂ, ∀ v, T v = c • v
  classification : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Algebra n →ₐ[ℂ] Module.End ℂ H), IsLeast n ρ →
      ∃ U : H ≃ₗᵢ[ℂ] Space n, ∀ A x, U (ρ A x) = representation n A (U x)

theorem generated : Conclusions where
  faithful := representation_injective
  adjoint_compatible := representation_starCompatible
  constructed_least := representation_isLeast
  dimension := actual_dimension
  scalar_commutant := coefficient_commutant
  classification := fun n _ _ _ _ ρ hρ => least_unitarilyEquivalent n ρ hρ

end GeneratedFoundations.Arithmetic.HistoryModuleRepresentation
