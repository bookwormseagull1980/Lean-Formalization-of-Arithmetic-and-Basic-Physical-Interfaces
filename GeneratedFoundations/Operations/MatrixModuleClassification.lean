module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith

/-!
# Matrix-unit decomposition of an arbitrary matrix representation

For a unital algebra representation of `M_n(K)`, the image of one diagonal
matrix unit is its multiplicity space.  Explicit matrix-unit coordinates
give an intertwining linear equivalence and the resulting dimension formula.
For a matrix algebra acting on one finite factor, natural linear maps are
classified by a single map on the remaining factor.
-/

@[expose] public section

namespace GeneratedFoundations.Operations.MatrixModuleClassification

open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

section Nondegeneracy

variable {A : Type*} [Ring A] [Algebra K A]

def Nondegenerate (ρ : A →ₙₐ[K] Module.End K V) : Prop :=
  ∀ v : V, (∀ a : A, ρ a v = 0) → v = 0

theorem nondegenerate_map_one (ρ : A →ₙₐ[K] Module.End K V)
    (hρ : Nondegenerate ρ) : ρ 1 = 1 := by
  ext v
  change ρ 1 v = v
  apply sub_eq_zero.mp
  apply hρ
  intro a
  rw [map_sub]
  change (ρ a * ρ 1) v - ρ a v = 0
  rw [← map_mul, mul_one, sub_self]

theorem nondegenerate_iff_map_one (ρ : A →ₙₐ[K] Module.End K V) :
    Nondegenerate ρ ↔ ρ 1 = 1 := by
  constructor
  · exact nondegenerate_map_one ρ
  · intro hρ v hv
    have h := hv 1
    simpa [hρ] using h

def nondegenerateUnitalization (ρ : A →ₙₐ[K] Module.End K V)
    (hρ : Nondegenerate ρ) : A →ₐ[K] Module.End K V :=
  AlgHom.ofLinearMap (LinearMap.ofClass ρ) (nondegenerate_map_one ρ hρ) (map_mul ρ)

@[simp] theorem nondegenerateUnitalization_apply
    (ρ : A →ₙₐ[K] Module.End K V) (hρ : Nondegenerate ρ) (a : A) :
    nondegenerateUnitalization ρ hρ a = ρ a := rfl

end Nondegeneracy

abbrev Representation := Matrix ι ι K →ₐ[K] Module.End K V

def matrixUnit (ρ : Representation (K := K) (V := V) (ι := ι))
    (i j : ι) : Module.End K V :=
  ρ (Matrix.single i j 1)

@[simp] theorem matrixUnit_comp_same
    (ρ : Representation (K := K) (V := V) (ι := ι)) (i j k : ι) (v : V) :
    matrixUnit ρ i j (matrixUnit ρ j k v) = matrixUnit ρ i k v := by
  calc
    _ = (ρ (Matrix.single i j 1 * Matrix.single j k 1)) v := by
      rw [map_mul]
      rfl
    _ = _ := by simp [matrixUnit]

theorem matrixUnit_comp_ne
    (ρ : Representation (K := K) (V := V) (ι := ι))
    (i j k l : ι) (hjk : j ≠ k) (v : V) :
    matrixUnit ρ i j (matrixUnit ρ k l v) = 0 := by
  calc
    _ = (ρ (Matrix.single i j 1 * Matrix.single k l 1)) v := by
      rw [map_mul]
      rfl
    _ = 0 := by
      rw [Matrix.single_mul_single_of_ne (1 : K) i j k hjk 1, map_zero]
      rfl

theorem sum_diagonal_matrixUnits
    (ρ : Representation (K := K) (V := V) (ι := ι)) :
    (∑ i, matrixUnit ρ i i) = 1 := by
  simp only [matrixUnit, ← map_sum, Matrix.sum_single_one, map_one]

theorem sum_diagonal_matrixUnits_apply
    (ρ : Representation (K := K) (V := V) (ι := ι)) (v : V) :
    (∑ i, matrixUnit ρ i i v) = v := by
  have h := congrArg (fun f : Module.End K V => f v) (sum_diagonal_matrixUnits ρ)
  simpa using h

def multiplicitySpace
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) : Submodule K V :=
  LinearMap.range (matrixUnit ρ base base)

theorem diagonal_fixes_multiplicity
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι)
    (v : multiplicitySpace ρ base) : matrixUnit ρ base base (v : V) = v := by
  obtain ⟨w, hw⟩ := v.2
  rw [← hw]
  exact matrixUnit_comp_same ρ base base base w

def coordinate
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base i : ι) :
    V →ₗ[K] multiplicitySpace ρ base where
  toFun v := ⟨matrixUnit ρ base i v,
    matrixUnit ρ base i v, matrixUnit_comp_same ρ base base i v⟩
  map_add' v w := by
    apply Subtype.ext
    exact (matrixUnit ρ base i).map_add v w
  map_smul' r v := by
    apply Subtype.ext
    exact (matrixUnit ρ base i).map_smul r v

def toCoordinates
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) :
    V →ₗ[K] (ι → multiplicitySpace ρ base) :=
  LinearMap.pi (coordinate ρ base)

def reconstruct
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) :
    (ι → multiplicitySpace ρ base) →ₗ[K] V where
  toFun w := ∑ i, matrixUnit ρ i base (w i : V)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum]

theorem reconstruct_toCoordinates
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) (v : V) :
    reconstruct ρ base (toCoordinates ρ base v) = v := by
  change (∑ i, matrixUnit ρ i base (matrixUnit ρ base i v)) = v
  simp only [matrixUnit_comp_same]
  exact sum_diagonal_matrixUnits_apply ρ v

theorem toCoordinates_reconstruct
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι)
    (w : ι → multiplicitySpace ρ base) :
    toCoordinates ρ base (reconstruct ρ base w) = w := by
  ext i
  change matrixUnit ρ base i (∑ j, matrixUnit ρ j base (w j : V)) = (w i : V)
  rw [map_sum, Finset.sum_eq_single i]
  · rw [matrixUnit_comp_same]
    exact diagonal_fixes_multiplicity ρ base (w i)
  · intro j _ hji
    exact matrixUnit_comp_ne ρ base i j base hji.symm (w j : V)
  · simp

def multiplicityEquiv
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) :
    V ≃ₗ[K] (ι → multiplicitySpace ρ base) where
  __ := toCoordinates ρ base
  invFun := reconstruct ρ base
  left_inv := reconstruct_toCoordinates ρ base
  right_inv := toCoordinates_reconstruct ρ base

theorem matrixUnit_mul_eq_row (a : Matrix ι ι K) (base i : ι) :
    Matrix.single base i 1 * a = ∑ j, a i j • Matrix.single base j 1 := by
  ext k l
  by_cases hk : base = k <;>
    simp [Matrix.mul_apply, Matrix.single, Matrix.sum_apply,
      smul_eq_mul, hk]

theorem coordinate_intertwines
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι)
    (a : Matrix ι ι K) (v : V) (i : ι) :
    toCoordinates ρ base (ρ a v) i =
      ∑ j, a i j • toCoordinates ρ base v j := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change matrixUnit ρ base i (ρ a v) = ∑ j, a i j • matrixUnit ρ base j v
  calc
    _ = (ρ (Matrix.single base i 1 * a)) v := by
      rw [map_mul]
      rfl
    _ = (ρ (∑ j, a i j • Matrix.single base j 1)) v := by
      rw [matrixUnit_mul_eq_row]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, matrixUnit]

section FiniteDimension

variable [FiniteDimensional K V]

theorem finrank_eq_card_mul_multiplicity
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) :
    Module.finrank K V = Fintype.card ι * Module.finrank K (multiplicitySpace ρ base) := by
  rw [(multiplicityEquiv ρ base).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem faithful_multiplicity_pos
    (ρ : Representation (K := K) (V := V) (ι := ι)) (hρ : Function.Injective ρ)
    (base : ι) : 0 < Module.finrank K (multiplicitySpace ρ base) := by
  classical
  have hunit : matrixUnit ρ base base ≠ 0 := by
    intro hz
    have he : Matrix.single base base (1 : K) = 0 := by
      apply hρ
      simpa [matrixUnit] using hz
    have hentry := congrArg (fun a : Matrix ι ι K => a base base) he
    simp at hentry
  have hex : ∃ v : V, matrixUnit ρ base base v ≠ 0 := by
    by_contra h
    apply hunit
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨matrixUnit ρ base base v, v, rfl⟩, ?_⟩
  intro hz
  apply hv
  exact congrArg Subtype.val hz

theorem faithful_finrank_lowerBound
    (ρ : Representation (K := K) (V := V) (ι := ι)) (hρ : Function.Injective ρ)
    (base : ι) : Fintype.card ι ≤ Module.finrank K V := by
  rw [finrank_eq_card_mul_multiplicity ρ base]
  have hp := faithful_multiplicity_pos ρ hρ base
  simpa using Nat.mul_le_mul_left (Fintype.card ι) hp

theorem minimal_finrank_iff_multiplicity_one
    (ρ : Representation (K := K) (V := V) (ι := ι)) (base : ι) :
    Module.finrank K V = Fintype.card ι ↔
      Module.finrank K (multiplicitySpace ρ base) = 1 := by
  rw [finrank_eq_card_mul_multiplicity ρ base]
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨base⟩
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_one]

end FiniteDimension

section HilbertRepresentations

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Compatibility with the actual Hilbert adjoint, rather than merely with
    an algebraic change of coordinates. -/
def StarCompatible (ρ : Representation (K := ℂ) (V := H) (ι := ι)) : Prop :=
  ∀ a x y, inner ℂ (ρ a x) y = inner ℂ x (ρ a.conjTranspose y)

theorem matrixUnit_inner
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (i j : ι) (x y : H) :
    inner ℂ (matrixUnit ρ i j x) y = inner ℂ x (matrixUnit ρ j i y) := by
  simpa [matrixUnit, Matrix.conjTranspose_single] using hρ (Matrix.single i j 1) x y

abbrev CoordinatesL2 (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (base : ι) :=
  PiLp 2 fun _ : ι => multiplicitySpace ρ base

noncomputable def coordinatesL2Equiv
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (base : ι) :
    H ≃ₗ[ℂ] CoordinatesL2 ρ base :=
  (multiplicityEquiv ρ base).trans
    (WithLp.linearEquiv 2 ℂ (ι → multiplicitySpace ρ base)).symm

theorem coordinatesL2_inner
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (base : ι) (x y : H) :
    inner ℂ (coordinatesL2Equiv ρ base x) (coordinatesL2Equiv ρ base y) =
      inner ℂ x y := by
  change (∑ i, inner ℂ (matrixUnit ρ base i x) (matrixUnit ρ base i y)) = _
  simp_rw [matrixUnit_inner ρ hρ, matrixUnit_comp_same]
  rw [← inner_sum, sum_diagonal_matrixUnits_apply]

noncomputable def multiplicityUnitary
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (base : ι) : H ≃ₗᵢ[ℂ] CoordinatesL2 ρ base :=
  (coordinatesL2Equiv ρ base).isometryOfInner (coordinatesL2_inner ρ hρ base)

theorem multiplicityUnitary_intertwines
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (base : ι) (a : Matrix ι ι ℂ) (x : H) (i : ι) :
    multiplicityUnitary ρ hρ base (ρ a x) i =
      ∑ j, a i j • multiplicityUnitary ρ hρ base x j :=
  coordinate_intertwines ρ base a x i

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

noncomputable def transportUnitary
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (σ : Representation (K := ℂ) (V := H') (ι := ι)) (hσ : StarCompatible σ)
    (base : ι) (e : multiplicitySpace ρ base ≃ₗᵢ[ℂ] multiplicitySpace σ base) :
    H ≃ₗᵢ[ℂ] H' :=
  (multiplicityUnitary ρ hρ base).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : ι => e).trans
      (multiplicityUnitary σ hσ base).symm)

theorem transportUnitary_coordinates
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (σ : Representation (K := ℂ) (V := H') (ι := ι)) (hσ : StarCompatible σ)
    (base : ι) (e : multiplicitySpace ρ base ≃ₗᵢ[ℂ] multiplicitySpace σ base)
    (x : H) (i : ι) :
    multiplicityUnitary σ hσ base (transportUnitary ρ hρ σ hσ base e x) i =
      e (multiplicityUnitary ρ hρ base x i) := by
  simp [transportUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply]

theorem transportUnitary_intertwines
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (σ : Representation (K := ℂ) (V := H') (ι := ι)) (hσ : StarCompatible σ)
    (base : ι) (e : multiplicitySpace ρ base ≃ₗᵢ[ℂ] multiplicitySpace σ base)
    (a : Matrix ι ι ℂ) (x : H) :
    transportUnitary ρ hρ σ hσ base e (ρ a x) =
      σ a (transportUnitary ρ hρ σ hσ base e x) := by
  apply (multiplicityUnitary σ hσ base).injective
  ext i
  rw [transportUnitary_coordinates, multiplicityUnitary_intertwines,
    multiplicityUnitary_intertwines]
  simp_rw [transportUnitary_coordinates]
  simp

/-- The realization is unique up to a unitary intertwiner. This does not
    assert that the intertwiner itself is unique. -/
theorem minimalFaithfulRepresentation_unique
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ H']
    (ρ : Representation (K := ℂ) (V := H) (ι := ι)) (hρ : StarCompatible ρ)
    (σ : Representation (K := ℂ) (V := H') (ι := ι)) (hσ : StarCompatible σ)
    (base : ι) (hminρ : Module.finrank ℂ H = Fintype.card ι)
    (hminσ : Module.finrank ℂ H' = Fintype.card ι) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) := by
  have hdimρ := (minimal_finrank_iff_multiplicity_one ρ base).mp hminρ
  have hdimσ := (minimal_finrank_iff_multiplicity_one σ base).mp hminσ
  let e : multiplicitySpace ρ base ≃ₗᵢ[ℂ] multiplicitySpace σ base :=
    (stdOrthonormalBasis ℂ (multiplicitySpace ρ base)).equiv
      (stdOrthonormalBasis ℂ (multiplicitySpace σ base))
      (finCongr (hdimρ.trans hdimσ.symm))
  exact ⟨transportUnitary ρ hρ σ hσ base e,
    transportUnitary_intertwines ρ hρ σ hσ base e⟩

end HilbertRepresentations

section NaturalMaps

variable {W : Type*} [AddCommGroup W] [Module K W]

def factorAction (a : Matrix ι ι K) : (ι → V) →ₗ[K] (ι → V) where
  toFun v i := ∑ j, a i j • v j
  map_add' v w := by
    ext i
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem factorAction_matrixUnit (i j : ι) (v : ι → V) :
    factorAction (Matrix.single i j (1 : K)) v = Pi.single i (v j) := by
  ext k
  by_cases hik : i = k
  · subst k
    simp [factorAction, Matrix.single]
  · simp [factorAction, Matrix.single, hik, Ne.symm hik]

def IsNatural (T : (ι → V) →ₗ[K] (ι → W)) : Prop :=
  ∀ (a : Matrix ι ι K) v, T (factorAction a v) = factorAction a (T v)

def reducedMap (T : (ι → V) →ₗ[K] (ι → W)) (base : ι) : V →ₗ[K] W :=
  (LinearMap.proj base).comp (T.comp (LinearMap.single K (fun _ : ι => V) base))

theorem natural_single (T : (ι → V) →ₗ[K] (ι → W)) (hT : IsNatural T)
    (base i : ι) (v : V) :
    T (Pi.single i v) = Pi.single i (reducedMap T base v) := by
  have h := hT (Matrix.single i base 1) (Pi.single base v)
  simpa [factorAction_matrixUnit, reducedMap] using h

theorem natural_apply (T : (ι → V) →ₗ[K] (ι → W)) (hT : IsNatural T)
    (base : ι) (v : ι → V) (i : ι) :
    T v i = reducedMap T base (v i) := by
  have hdecomp : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
  rw [hdecomp, map_sum]
  simp_rw [natural_single T hT base]
  simp

theorem natural_iff_existsUnique_reducedMap
    (T : (ι → V) →ₗ[K] (ι → W)) (base : ι) :
    IsNatural T ↔ ∃! h : V →ₗ[K] W, ∀ v i, T v i = h (v i) := by
  constructor
  · intro hT
    refine ⟨reducedMap T base, natural_apply T hT base, ?_⟩
    intro h hh
    ext v
    have hvalue := hh (Pi.single base v) base
    simpa [reducedMap] using hvalue.symm
  · rintro ⟨h, hh, _⟩ a v
    ext i
    rw [hh]
    change h (∑ j, a i j • v j) = ∑ j, a i j • T v j
    simp_rw [hh]
    simp

end NaturalMaps

end GeneratedFoundations.Operations.MatrixModuleClassification
