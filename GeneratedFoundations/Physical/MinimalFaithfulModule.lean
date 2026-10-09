module

public import GeneratedFoundations.Physical.MatrixModuleClassification
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Faithful representations of finite sums of full matrix algebras

The multiplicity spaces are the ranges of represented diagonal matrix
units.  The coordinate decomposition is constructed for an arbitrary
unital representation; neither a block decomposition of its carrier nor
irreducibility is assumed.
-/

@[expose] public section

namespace GeneratedFoundations.Physical.MinimalFaithfulModule

open scoped BigOperators

variable {K V B : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype B] [DecidableEq B] (n : B → ℕ)

abbrev BlockAlgebra := ∀ b : B, Matrix (Fin (n b)) (Fin (n b)) K

abbrev Representation := BlockAlgebra (K := K) n →ₐ[K] Module.End K V

def algebraUnit (b : B) (i j : Fin (n b)) : BlockAlgebra (K := K) n :=
  Pi.single b (Matrix.single i j 1)

def matrixUnit (ρ : Representation (K := K) (V := V) n)
    (b : B) (i j : Fin (n b)) : Module.End K V :=
  ρ (algebraUnit n b i j)

omit [Fintype B] in
theorem algebraUnit_mul_same (b : B) (i j k : Fin (n b)) :
    algebraUnit (K := K) n b i j * algebraUnit n b j k =
      algebraUnit n b i k := by
  ext c r s
  by_cases h : b = c
  · subst c
    simp [algebraUnit]
  · simp [algebraUnit, h]

omit [Fintype B] in
theorem algebraUnit_mul_ne (b : B) (i j k l : Fin (n b)) (hjk : j ≠ k) :
    algebraUnit (K := K) n b i j * algebraUnit n b k l = 0 := by
  ext c r s
  by_cases h : b = c
  · subst c
    simp [algebraUnit, Matrix.single_mul_single_of_ne (1 : K) i j k hjk 1]
  · simp [algebraUnit, h]

omit [Fintype B] in
theorem algebraUnit_mul_other (b c : B) (hbc : b ≠ c)
    (i j : Fin (n b)) (k l : Fin (n c)) :
    algebraUnit (K := K) n b i j * algebraUnit n c k l = 0 := by
  ext d r s
  by_cases hb : b = d
  · subst d
    simp [algebraUnit, Ne.symm hbc]
  · simp [algebraUnit, hb]

omit [Fintype B] in
@[simp] theorem matrixUnit_comp_same
    (ρ : Representation (K := K) (V := V) n) (b : B)
    (i j k : Fin (n b)) (v : V) :
    matrixUnit n ρ b i j (matrixUnit n ρ b j k v) = matrixUnit n ρ b i k v := by
  change (ρ (algebraUnit n b i j) * ρ (algebraUnit n b j k)) v = _
  rw [← map_mul, algebraUnit_mul_same]
  rfl

omit [Fintype B] in
theorem matrixUnit_comp_ne
    (ρ : Representation (K := K) (V := V) n) (b : B)
    (i j k l : Fin (n b)) (hjk : j ≠ k) (v : V) :
    matrixUnit n ρ b i j (matrixUnit n ρ b k l v) = 0 := by
  change (ρ (algebraUnit n b i j) * ρ (algebraUnit n b k l)) v = 0
  rw [← map_mul, algebraUnit_mul_ne n b i j k l hjk, map_zero]
  rfl

omit [Fintype B] in
theorem matrixUnit_comp_other
    (ρ : Representation (K := K) (V := V) n) (b c : B) (hbc : b ≠ c)
    (i j : Fin (n b)) (k l : Fin (n c)) (v : V) :
    matrixUnit n ρ b i j (matrixUnit n ρ c k l v) = 0 := by
  change (ρ (algebraUnit n b i j) * ρ (algebraUnit n c k l)) v = 0
  rw [← map_mul, algebraUnit_mul_other n b c hbc i j k l, map_zero]
  rfl

theorem sum_algebraUnits : (∑ b, ∑ i, algebraUnit (K := K) n b i i) = 1 := by
  funext b
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · simp only [algebraUnit, Pi.single_eq_same]
    exact Matrix.sum_single_one
  · intro c _ hcb
    simp [algebraUnit, hcb]
  · simp

theorem sum_matrixUnits (ρ : Representation (K := K) (V := V) n) (v : V) :
    (∑ b, ∑ i, matrixUnit n ρ b i i v) = v := by
  have h := congrArg (fun a : BlockAlgebra (K := K) n => ρ a v)
    (sum_algebraUnits (K := K) n)
  simpa [matrixUnit, map_sum] using h

def multiplicitySpace (ρ : Representation (K := K) (V := V) n)
    (base : ∀ b, Fin (n b)) (b : B) : Submodule K V :=
  LinearMap.range (matrixUnit n ρ b (base b) (base b))

omit [Fintype B] in
theorem diagonal_fixes_multiplicity
    (ρ : Representation (K := K) (V := V) n) (base : ∀ b, Fin (n b))
    (b : B) (v : multiplicitySpace n ρ base b) :
    matrixUnit n ρ b (base b) (base b) (v : V) = v := by
  obtain ⟨w, hw⟩ := v.2
  rw [← hw]
  exact matrixUnit_comp_same n ρ b (base b) (base b) (base b) w

def coordinate (ρ : Representation (K := K) (V := V) n)
    (base : ∀ b, Fin (n b)) (b : B) (i : Fin (n b)) :
    V →ₗ[K] multiplicitySpace n ρ base b where
  toFun v := ⟨matrixUnit n ρ b (base b) i v,
    matrixUnit n ρ b (base b) i v,
    matrixUnit_comp_same n ρ b (base b) (base b) i v⟩
  map_add' v w := by
    apply Subtype.ext
    exact (matrixUnit n ρ b (base b) i).map_add v w
  map_smul' r v := by
    apply Subtype.ext
    exact (matrixUnit n ρ b (base b) i).map_smul r v

def toCoordinates (ρ : Representation (K := K) (V := V) n)
    (base : ∀ b, Fin (n b)) :
    V →ₗ[K] (∀ b, Fin (n b) → multiplicitySpace n ρ base b) :=
  LinearMap.pi fun b => LinearMap.pi (coordinate n ρ base b)

def reconstruct (ρ : Representation (K := K) (V := V) n)
    (base : ∀ b, Fin (n b)) :
    (∀ b, Fin (n b) → multiplicitySpace n ρ base b) →ₗ[K] V where
  toFun w := ∑ b, ∑ i, matrixUnit n ρ b i (base b) (w b i : V)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum]

theorem reconstruct_toCoordinates
    (ρ : Representation (K := K) (V := V) n) (base : ∀ b, Fin (n b)) (v : V) :
    reconstruct n ρ base (toCoordinates n ρ base v) = v := by
  change (∑ b, ∑ i,
    matrixUnit n ρ b i (base b) (matrixUnit n ρ b (base b) i v)) = v
  simp only [matrixUnit_comp_same]
  exact sum_matrixUnits n ρ v

theorem toCoordinates_reconstruct
    (ρ : Representation (K := K) (V := V) n) (base : ∀ b, Fin (n b))
    (w : ∀ b, Fin (n b) → multiplicitySpace n ρ base b) :
    toCoordinates n ρ base (reconstruct n ρ base w) = w := by
  ext b i
  change matrixUnit n ρ b (base b) i
    (∑ c, ∑ j, matrixUnit n ρ c j (base c) (w c j : V)) = (w b i : V)
  rw [map_sum, Finset.sum_eq_single b]
  · rw [map_sum, Finset.sum_eq_single i]
    · rw [matrixUnit_comp_same]
      exact diagonal_fixes_multiplicity n ρ base b (w b i)
    · intro j _ hji
      exact matrixUnit_comp_ne n ρ b (base b) i j (base b) hji.symm (w b j : V)
    · simp
  · intro c _ hcb
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact matrixUnit_comp_other n ρ b c hcb.symm (base b) i j (base c) (w c j : V)
  · simp

def multiplicityEquiv (ρ : Representation (K := K) (V := V) n)
    (base : ∀ b, Fin (n b)) :
    V ≃ₗ[K] (∀ b, Fin (n b) → multiplicitySpace n ρ base b) where
  __ := toCoordinates n ρ base
  invFun := reconstruct n ρ base
  left_inv := reconstruct_toCoordinates n ρ base
  right_inv := toCoordinates_reconstruct n ρ base

omit [Fintype B] in
theorem algebraUnit_mul_eq_row (a : BlockAlgebra (K := K) n)
    (b : B) (base i : Fin (n b)) :
    algebraUnit n b base i * a = ∑ j, a b i j • algebraUnit n b base j := by
  ext c r s
  by_cases h : b = c
  · subst c
    simpa [algebraUnit, Finset.sum_apply] using
      congrArg (fun m : Matrix (Fin (n b)) (Fin (n b)) K => m r s)
        (MatrixModuleClassification.matrixUnit_mul_eq_row (a b) base i)
  · simp [algebraUnit, h, Finset.sum_apply]

omit [Fintype B] in
theorem coordinate_intertwines
    (ρ : Representation (K := K) (V := V) n) (base : ∀ b, Fin (n b))
    (a : BlockAlgebra (K := K) n) (v : V) (b : B) (i : Fin (n b)) :
    toCoordinates n ρ base (ρ a v) b i =
      ∑ j, a b i j • toCoordinates n ρ base v b j := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change matrixUnit n ρ b (base b) i (ρ a v) =
    ∑ j, a b i j • matrixUnit n ρ b (base b) j v
  calc
    _ = (ρ (algebraUnit n b (base b) i * a)) v := by
      rw [map_mul]
      rfl
    _ = (ρ (∑ j, a b i j • algebraUnit n b (base b) j)) v := by
      rw [algebraUnit_mul_eq_row]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, matrixUnit]

def standardRepresentation : Representation (K := K) (V := ∀ b, Fin (n b) → K) n where
  toFun a := LinearMap.piMap fun b => Matrix.toLinAlgEquiv' (a b)
  map_zero' := by
    apply LinearMap.ext
    intro x
    funext b i
    simp [LinearMap.piMap]
  map_one' := by
    apply LinearMap.ext
    intro x
    funext b i
    simp [LinearMap.piMap]
  map_add' a c := by
    apply LinearMap.ext
    intro x
    funext b i
    simp [LinearMap.piMap]
  map_mul' a c := by
    apply LinearMap.ext
    intro x
    funext b i
    change (a b * c b).mulVec (x b) i = (a b).mulVec ((c b).mulVec (x b)) i
    rw [Matrix.mulVec_mulVec]
  commutes' r := by
    apply LinearMap.ext
    intro x
    funext b i
    change Matrix.toLinAlgEquiv' (algebraMap K (Matrix (Fin (n b)) (Fin (n b)) K) r)
      (x b) i = r * x b i
    rw [AlgEquiv.commutes]
    rfl

omit [Fintype B] in
theorem standardRepresentation_injective :
    Function.Injective (standardRepresentation (K := K) n) := by
  intro a c hac
  ext b i j
  have h := congrArg (fun T : Module.End K (∀ b, Fin (n b) → K) =>
    T (Pi.single b (Pi.single j 1)) b i) hac
  simpa [standardRepresentation, LinearMap.piMap] using h

omit [DecidableEq B] in
theorem standardRepresentation_finrank :
    Module.finrank K (∀ b, Fin (n b) → K) = ∑ b, n b := by
  simp [Module.finrank_pi_fintype]

section FiniteDimension

variable [FiniteDimensional K V]

theorem finrank_eq_sum_multiplicities
    (ρ : Representation (K := K) (V := V) n) (base : ∀ b, Fin (n b)) :
    Module.finrank K V = ∑ b, n b * Module.finrank K (multiplicitySpace n ρ base b) := by
  rw [(multiplicityEquiv n ρ base).finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype]

omit [Fintype B] in
theorem faithful_multiplicity_pos
    (ρ : Representation (K := K) (V := V) n) (hρ : Function.Injective ρ)
    (base : ∀ b, Fin (n b)) (b : B) :
    0 < Module.finrank K (multiplicitySpace n ρ base b) := by
  classical
  have hunit : matrixUnit n ρ b (base b) (base b) ≠ 0 := by
    intro hz
    have he : algebraUnit (K := K) n b (base b) (base b) = 0 := by
      apply hρ
      simpa [matrixUnit] using hz
    have hentry := congrArg (fun a : BlockAlgebra (K := K) n => a b (base b) (base b)) he
    simp [algebraUnit] at hentry
  have hex : ∃ v : V, matrixUnit n ρ b (base b) (base b) v ≠ 0 := by
    by_contra h
    apply hunit
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨matrixUnit n ρ b (base b) (base b) v, v, rfl⟩, ?_⟩
  intro hz
  apply hv
  exact congrArg Subtype.val hz

theorem faithful_finrank_lowerBound
    (ρ : Representation (K := K) (V := V) n) (hρ : Function.Injective ρ)
    (base : ∀ b, Fin (n b)) : (∑ b, n b) ≤ Module.finrank K V := by
  rw [finrank_eq_sum_multiplicities n ρ base]
  apply Finset.sum_le_sum
  intro b _
  have hp := faithful_multiplicity_pos n ρ hρ base b
  simpa using Nat.mul_le_mul_left (n b) hp

theorem minimal_finrank_iff_multiplicities_one
    (ρ : Representation (K := K) (V := V) n) (hρ : Function.Injective ρ)
    (base : ∀ b, Fin (n b)) :
    Module.finrank K V = ∑ b, n b ↔
      ∀ b, Module.finrank K (multiplicitySpace n ρ base b) = 1 := by
  rw [finrank_eq_sum_multiplicities n ρ base]
  constructor
  · intro he b
    have hle : ∀ c : B, n c ≤ n c * Module.finrank K (multiplicitySpace n ρ base c) := by
      intro c
      have hp := faithful_multiplicity_pos n ρ hρ base c
      simpa using Nat.mul_le_mul_left (n c) hp
    have hp := faithful_multiplicity_pos n ρ hρ base b
    have hn : 0 < n b := Nat.zero_lt_of_lt (base b).isLt
    by_contra hne
    have hk : 1 < Module.finrank K (multiplicitySpace n ρ base b) := by omega
    have hs : (∑ c, n c) < ∑ c, n c * Module.finrank K (multiplicitySpace n ρ base c) := by
      apply Finset.sum_lt_sum (fun c _ => hle c)
      refine ⟨b, Finset.mem_univ b, ?_⟩
      simpa using Nat.mul_lt_mul_of_pos_left hk hn
    omega
  · intro h
    simp [h]

end FiniteDimension

section HilbertSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def blockAdjoint (a : BlockAlgebra (K := ℂ) n) : BlockAlgebra (K := ℂ) n :=
  fun b => (a b).conjTranspose

/-- Preservation of the matrix adjoint, written through its defining
inner-product identity. -/
def StarCompatible (ρ : Representation (K := ℂ) (V := H) n) : Prop :=
  ∀ a x y, inner ℂ (ρ a x) y = inner ℂ x (ρ (blockAdjoint n a) y)

abbrev StandardHilbert := PiLp 2 fun b : B => EuclideanSpace ℂ (Fin (n b))

noncomputable def standardHilbertCoordinates :
    (∀ b, Fin (n b) → ℂ) ≃ₗ[ℂ] StandardHilbert n :=
  (LinearEquiv.piCongrRight fun b =>
    (WithLp.linearEquiv 2 ℂ (Fin (n b) → ℂ)).symm).trans
      (WithLp.linearEquiv 2 ℂ (∀ b, EuclideanSpace ℂ (Fin (n b)))).symm

noncomputable def standardHilbertRepresentation :
    Representation (K := ℂ) (V := StandardHilbert n) n :=
  ((standardHilbertCoordinates n).conjAlgEquiv ℂ).toAlgHom.comp
    (standardRepresentation (K := ℂ) n)

omit [Fintype B] [DecidableEq B] in
theorem standardHilbertRepresentation_apply
    (a : BlockAlgebra (K := ℂ) n) (x : StandardHilbert n) (b : B) (i : Fin (n b)) :
    standardHilbertRepresentation n a x b i = ∑ j, a b i j * x b j := rfl

omit [Fintype B] in
theorem standardHilbertRepresentation_injective :
    Function.Injective (standardHilbertRepresentation n) :=
  ((standardHilbertCoordinates n).conjAlgEquiv ℂ).injective.comp
    (standardRepresentation_injective n)

omit [DecidableEq B] in
theorem standardHilbertRepresentation_finrank :
    Module.finrank ℂ (StandardHilbert n) = ∑ b, n b := by
  rw [← (standardHilbertCoordinates n).finrank_eq]
  exact standardRepresentation_finrank n

omit [DecidableEq B] in
theorem standardHilbertRepresentation_starCompatible :
    StarCompatible n (standardHilbertRepresentation n) := by
  intro a x y
  simp only [PiLp.inner_apply, RCLike.inner_apply', standardHilbertRepresentation_apply,
    blockAdjoint, Matrix.conjTranspose_apply, RCLike.star_def, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype B] in
theorem blockAdjoint_algebraUnit (b : B) (i j : Fin (n b)) :
    blockAdjoint n (algebraUnit (K := ℂ) n b i j) = algebraUnit n b j i := by
  funext c
  by_cases h : b = c
  · subst c
    simp only [blockAdjoint, algebraUnit, Pi.single_eq_same, Matrix.conjTranspose_single, star_one]
  · simp [blockAdjoint, algebraUnit, h]

omit [Fintype B] in
theorem matrixUnit_inner
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (b : B) (i j : Fin (n b)) (x y : H) :
    inner ℂ (matrixUnit n ρ b i j x) y =
      inner ℂ x (matrixUnit n ρ b j i y) := by
  simpa [matrixUnit, blockAdjoint_algebraUnit] using
    hρ (algebraUnit n b i j) x y

abbrev CoordinatesL2 (ρ : Representation (K := ℂ) (V := H) n)
    (base : ∀ b, Fin (n b)) :=
  PiLp 2 fun b => PiLp 2 fun _ : Fin (n b) => multiplicitySpace n ρ base b

noncomputable def coordinatesL2Equiv
    (ρ : Representation (K := ℂ) (V := H) n) (base : ∀ b, Fin (n b)) :
    H ≃ₗ[ℂ] CoordinatesL2 n ρ base :=
  (multiplicityEquiv n ρ base).trans
    ((LinearEquiv.piCongrRight fun b =>
      (WithLp.linearEquiv 2 ℂ (Fin (n b) → multiplicitySpace n ρ base b)).symm).trans
        (WithLp.linearEquiv 2 ℂ
          (∀ b, PiLp 2 fun _ : Fin (n b) => multiplicitySpace n ρ base b)).symm)

theorem coordinatesL2_inner
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (base : ∀ b, Fin (n b)) (x y : H) :
    inner ℂ (coordinatesL2Equiv n ρ base x) (coordinatesL2Equiv n ρ base y) =
      inner ℂ x y := by
  change (∑ b, ∑ i, inner ℂ
    (matrixUnit n ρ b (base b) i x) (matrixUnit n ρ b (base b) i y)) = _
  simp_rw [matrixUnit_inner n ρ hρ, matrixUnit_comp_same]
  simp_rw [← inner_sum]
  rw [sum_matrixUnits]

noncomputable def multiplicityUnitary
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (base : ∀ b, Fin (n b)) : H ≃ₗᵢ[ℂ] CoordinatesL2 n ρ base :=
  (coordinatesL2Equiv n ρ base).isometryOfInner (coordinatesL2_inner n ρ hρ base)

theorem multiplicityUnitary_intertwines
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (base : ∀ b, Fin (n b)) (a : BlockAlgebra (K := ℂ) n)
    (x : H) (b : B) (i : Fin (n b)) :
    multiplicityUnitary n ρ hρ base (ρ a x) b i =
      ∑ j, a b i j • multiplicityUnitary n ρ hρ base x b j :=
  coordinate_intertwines n ρ base a x b i

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

noncomputable def transportUnitary
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (σ : Representation (K := ℂ) (V := H') n) (hσ : StarCompatible n σ)
    (base : ∀ b, Fin (n b))
    (e : ∀ b, multiplicitySpace n ρ base b ≃ₗᵢ[ℂ] multiplicitySpace n σ base b) :
    H ≃ₗᵢ[ℂ] H' :=
  (multiplicityUnitary n ρ hρ base).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 fun b =>
      LinearIsometryEquiv.piLpCongrRight 2 fun _ : Fin (n b) => e b).trans
        (multiplicityUnitary n σ hσ base).symm)

theorem transportUnitary_coordinates
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (σ : Representation (K := ℂ) (V := H') n) (hσ : StarCompatible n σ)
    (base : ∀ b, Fin (n b))
    (e : ∀ b, multiplicitySpace n ρ base b ≃ₗᵢ[ℂ] multiplicitySpace n σ base b)
    (x : H) (b : B) (i : Fin (n b)) :
    multiplicityUnitary n σ hσ base (transportUnitary n ρ hρ σ hσ base e x) b i =
      e b (multiplicityUnitary n ρ hρ base x b i) := by
  simp [transportUnitary, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply]

theorem transportUnitary_intertwines
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (σ : Representation (K := ℂ) (V := H') n) (hσ : StarCompatible n σ)
    (base : ∀ b, Fin (n b))
    (e : ∀ b, multiplicitySpace n ρ base b ≃ₗᵢ[ℂ] multiplicitySpace n σ base b)
    (a : BlockAlgebra (K := ℂ) n) (x : H) :
    transportUnitary n ρ hρ σ hσ base e (ρ a x) =
      σ a (transportUnitary n ρ hρ σ hσ base e x) := by
  apply (multiplicityUnitary n σ hσ base).injective
  ext b i
  rw [transportUnitary_coordinates, multiplicityUnitary_intertwines,
    multiplicityUnitary_intertwines]
  simp_rw [transportUnitary_coordinates]
  simp

theorem minimalFaithfulJointRep_unique
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ H']
    (ρ : Representation (K := ℂ) (V := H) n) (hρ : StarCompatible n ρ)
    (hρinj : Function.Injective ρ)
    (σ : Representation (K := ℂ) (V := H') n) (hσ : StarCompatible n σ)
    (hσinj : Function.Injective σ) (base : ∀ b, Fin (n b))
    (hminρ : Module.finrank ℂ H = ∑ b, n b)
    (hminσ : Module.finrank ℂ H' = ∑ b, n b) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) := by
  classical
  have hdimρ := (minimal_finrank_iff_multiplicities_one n ρ hρinj base).mp hminρ
  have hdimσ := (minimal_finrank_iff_multiplicities_one n σ hσinj base).mp hminσ
  let e (b : B) : multiplicitySpace n ρ base b ≃ₗᵢ[ℂ] multiplicitySpace n σ base b :=
    (stdOrthonormalBasis ℂ (multiplicitySpace n ρ base b)).equiv
      (stdOrthonormalBasis ℂ (multiplicitySpace n σ base b))
      (finCongr ((hdimρ b).trans (hdimσ b).symm))
  refine ⟨transportUnitary n ρ hρ σ hσ base e, ?_⟩
  exact transportUnitary_intertwines n ρ hρ σ hσ base e

end HilbertSpace

section JointResponse

def jointBlockSizes : Bool → ℕ
  | true => 6
  | false => 2

abbrev JointAlgebra :=
  Matrix (Fin 6) (Fin 6) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- The two-block family notation and the direct-product notation for the
six-dimensional and two-dimensional matrix blocks. -/
def jointAlgebraEquiv : BlockAlgebra (K := ℂ) jointBlockSizes ≃ₐ[ℂ] JointAlgebra where
  toFun a := (a true, a false)
  invFun a := fun b => match b with
    | true => a.1
    | false => a.2
  left_inv a := by
    funext b
    cases b <;> rfl
  right_inv a := rfl
  map_mul' a b := rfl
  map_add' a b := rfl
  commutes' r := rfl

def jointBase (b : Bool) : Fin (jointBlockSizes b) :=
  ⟨0, by cases b <;> decide⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

abbrev JointRepresentation := JointAlgebra →ₐ[ℂ] Module.End ℂ H

noncomputable def jointBlockRepresentation (ρ : JointRepresentation (H := H)) :
    Representation (K := ℂ) (V := H) jointBlockSizes :=
  ρ.comp jointAlgebraEquiv.toAlgHom

def JointStarCompatible (ρ : JointRepresentation (H := H)) : Prop :=
  ∀ a x y, inner ℂ (ρ a x) y =
    inner ℂ x (ρ (a.1.conjTranspose, a.2.conjTranspose) y)

theorem jointAlgebraEquiv_symm_adjoint (a : JointAlgebra) :
    blockAdjoint jointBlockSizes (jointAlgebraEquiv.symm a) =
      jointAlgebraEquiv.symm (a.1.conjTranspose, a.2.conjTranspose) := by
  funext b
  cases b <;> rfl

noncomputable def standardJointRepresentation :
    JointRepresentation (H := StandardHilbert jointBlockSizes) :=
  (standardHilbertRepresentation jointBlockSizes).comp jointAlgebraEquiv.symm.toAlgHom

theorem standardJointRepresentation_injective :
    Function.Injective standardJointRepresentation :=
  (standardHilbertRepresentation_injective jointBlockSizes).comp jointAlgebraEquiv.symm.injective

theorem standardJointRepresentation_starCompatible :
    JointStarCompatible standardJointRepresentation := by
  intro a x y
  change inner ℂ (standardHilbertRepresentation jointBlockSizes (jointAlgebraEquiv.symm a) x) y =
    inner ℂ x (standardHilbertRepresentation jointBlockSizes
      (jointAlgebraEquiv.symm (a.1.conjTranspose, a.2.conjTranspose)) y)
  rw [← jointAlgebraEquiv_symm_adjoint]
  exact standardHilbertRepresentation_starCompatible jointBlockSizes (jointAlgebraEquiv.symm a) x y

theorem standardJointRepresentation_finrank :
    Module.finrank ℂ (StandardHilbert jointBlockSizes) = 8 := by
  simpa [jointBlockSizes] using standardHilbertRepresentation_finrank jointBlockSizes

omit [FiniteDimensional ℂ H] in
theorem jointBlockRepresentation_starCompatible
    (ρ : JointRepresentation (H := H)) (hρ : JointStarCompatible ρ) :
    StarCompatible jointBlockSizes (jointBlockRepresentation ρ) := by
  intro a x y
  exact hρ (jointAlgebraEquiv a) x y

theorem faithfulJointRep_finrank_ge_eight
    (ρ : JointRepresentation (H := H)) (hρ : Function.Injective ρ) :
    8 ≤ Module.finrank ℂ H := by
  have h := faithful_finrank_lowerBound jointBlockSizes (jointBlockRepresentation ρ)
    (hρ.comp jointAlgebraEquiv.injective) jointBase
  simpa [jointBlockSizes] using h

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- Every two faithful adjoint-preserving eight-dimensional realizations
of the joint response algebra are unitarily equivalent. -/
theorem minimalEightDimensionalJointRep_unique
    (ρ : JointRepresentation (H := H)) (hρ : JointStarCompatible ρ)
    (hρinj : Function.Injective ρ)
    (σ : JointRepresentation (H := H')) (hσ : JointStarCompatible σ)
    (hσinj : Function.Injective σ)
    (hdimρ : Module.finrank ℂ H = 8) (hdimσ : Module.finrank ℂ H' = 8) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) := by
  have hminρ : Module.finrank ℂ H = ∑ b, jointBlockSizes b := by
    simpa [jointBlockSizes] using hdimρ
  have hminσ : Module.finrank ℂ H' = ∑ b, jointBlockSizes b := by
    simpa [jointBlockSizes] using hdimσ
  obtain ⟨U, hU⟩ := minimalFaithfulJointRep_unique jointBlockSizes
    (jointBlockRepresentation ρ) (jointBlockRepresentation_starCompatible ρ hρ)
    (hρinj.comp jointAlgebraEquiv.injective)
    (jointBlockRepresentation σ) (jointBlockRepresentation_starCompatible σ hσ)
    (hσinj.comp jointAlgebraEquiv.injective) jointBase hminρ hminσ
  refine ⟨U, ?_⟩
  intro a x
  simpa [jointBlockRepresentation] using hU (jointAlgebraEquiv.symm a) x

/-- Least dimension among faithful adjoint-preserving representations on
finite-dimensional complex Hilbert spaces. -/
def IsLeastFaithfulJointRepresentation (ρ : JointRepresentation (H := H)) : Prop :=
  Function.Injective ρ ∧ JointStarCompatible ρ ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      (σ : JointRepresentation (H := E)),
      Function.Injective σ → JointStarCompatible σ →
        Module.finrank ℂ H ≤ Module.finrank ℂ E

theorem standardJointRepresentation_isLeast :
    IsLeastFaithfulJointRepresentation standardJointRepresentation := by
  refine ⟨standardJointRepresentation_injective, standardJointRepresentation_starCompatible, ?_⟩
  intro E _ _ _ σ hσ _
  rw [standardJointRepresentation_finrank]
  exact faithfulJointRep_finrank_ge_eight σ hσ

theorem leastFaithfulJointRep_finrank_eight
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ) :
    Module.finrank ℂ H = 8 := by
  have hle := hρ.2.2 (StandardHilbert jointBlockSizes) standardJointRepresentation
    standardJointRepresentation_injective standardJointRepresentation_starCompatible
  rw [standardJointRepresentation_finrank] at hle
  exact Nat.le_antisymm hle (faithfulJointRep_finrank_ge_eight ρ hρ.1)

theorem leastFaithfulJointRep_unitarilyEquivalentToStandard
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] StandardHilbert jointBlockSizes,
      ∀ a x, U (ρ a x) = standardJointRepresentation a (U x) :=
  minimalEightDimensionalJointRep_unique ρ hρ.2.1 hρ.1
    standardJointRepresentation standardJointRepresentation_starCompatible
    standardJointRepresentation_injective (leastFaithfulJointRep_finrank_eight ρ hρ)
    standardJointRepresentation_finrank

theorem leastFaithfulJointRep_unique
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ)
    (σ : JointRepresentation (H := H')) (hσ : IsLeastFaithfulJointRepresentation σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) :=
  minimalEightDimensionalJointRep_unique ρ hρ.2.1 hρ.1 σ hσ.2.1 hσ.1
    (leastFaithfulJointRep_finrank_eight ρ hρ) (leastFaithfulJointRep_finrank_eight σ hσ)

theorem pairedFaithfulJointRep_finrank_ge_sixteen
    (ρ : JointRepresentation (H := H)) (hρ : Function.Injective ρ)
    (σ : JointRepresentation (H := H')) (hσ : Function.Injective σ) :
    16 ≤ Module.finrank ℂ (H × H') := by
  rw [Module.finrank_prod]
  have hleft := faithfulJointRep_finrank_ge_eight ρ hρ
  have hright := faithfulJointRep_finrank_ge_eight σ hσ
  omega

/-- The full left-right carrier retains both eight-dimensional modules.
No quotient by a neutral charge line is taken in this dimension count. -/
theorem pairedMinimalJointRep_finrank_sixteen
    (hdimρ : Module.finrank ℂ H = 8) (hdimσ : Module.finrank ℂ H' = 8) :
    Module.finrank ℂ (H × H') = 16 := by
  rw [Module.finrank_prod, hdimρ, hdimσ]

theorem pairedLeastFaithfulJointRep_finrank_sixteen
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ)
    (σ : JointRepresentation (H := H')) (hσ : IsLeastFaithfulJointRepresentation σ) :
    Module.finrank ℂ (H × H') = 16 :=
  pairedMinimalJointRep_finrank_sixteen
    (leastFaithfulJointRep_finrank_eight ρ hρ) (leastFaithfulJointRep_finrank_eight σ hσ)

end JointResponse

end GeneratedFoundations.Physical.MinimalFaithfulModule
