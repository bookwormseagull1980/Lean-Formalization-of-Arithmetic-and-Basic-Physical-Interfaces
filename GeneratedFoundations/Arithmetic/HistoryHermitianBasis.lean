module

public import GeneratedFoundations.Arithmetic.HistoryHermitianResponse

/-!
# Independent real generators of the complete arithmetic operation space

The real space consists of all Hermitian traceless matrices on the original
history--phase/source carrier. It inherits the complete coefficient metric,
not an unweighted metric on a selected list of entries. An orthonormal basis
of that actual space provides independent real generators and unique real
coordinates. The basis is a comparison coordinate choice; the subspace,
trace metric and represented operators are fixed before that choice.

The redundant centred frame and its calculated Casimir in
`HistoryHermitianResponse` remain unchanged. Its normalization is not
silently assigned to this orthonormal basis.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHermitianBasis

open HistoryCliffordAction (Index Algebra Space action)

abbrev Coefficients (N : ℕ) := EuclideanSpace ℂ (Index N × Index N)

def matrixMap (N : ℕ) : Coefficients N →ₗ[ℂ] Algebra N where
  toFun x i j := x (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem matrixMap_injective (N : ℕ) : Function.Injective (matrixMap N) := by
  intro x y h
  apply PiLp.ext
  rintro ⟨i, j⟩
  exact congrArg (fun A : Algebra N => A i j) h

def matrixCoefficients (N : ℕ) (X : Algebra N) : Coefficients N :=
  WithLp.toLp 2 fun ij => X ij.1 ij.2

@[simp] theorem matrixMap_coefficients (N : ℕ) (X : Algebra N) :
    matrixMap N (matrixCoefficients N X) = X := rfl

theorem matrixMap_surjective (N : ℕ) : Function.Surjective (matrixMap N) :=
  fun X => ⟨matrixCoefficients N X, matrixMap_coefficients N X⟩

def hermitianTraceless (N : ℕ) : Submodule ℝ (Coefficients N) where
  carrier := {x | (matrixMap N x).IsHermitian ∧ Matrix.trace (matrixMap N x) = 0}
  zero_mem' := by simp [matrixMap, Matrix.IsHermitian]
  add_mem' := by
    intro x y hx hy
    change (matrixMap N (x + y)).IsHermitian ∧ Matrix.trace (matrixMap N (x + y)) = 0
    rw [map_add]
    exact ⟨hx.1.add hy.1, by rw [Matrix.trace_add, hx.2, hy.2, add_zero]⟩
  smul_mem' := by
    intro t x hx
    have he : matrixMap N (t • x) = (t : ℂ) • matrixMap N x := by
      ext i j
      rfl
    change (matrixMap N (t • x)).IsHermitian ∧ Matrix.trace (matrixMap N (t • x)) = 0
    rw [he]
    constructor
    · change ((t : ℂ) • matrixMap N x).conjTranspose = _
      rw [Matrix.conjTranspose_smul, hx.1.eq]
      simp
    · rw [Matrix.trace_smul, hx.2, smul_zero]

abbrev GeneratorSpace (N : ℕ) := hermitianTraceless N
abbrev GeneratorIndex (N : ℕ) := Fin (Module.finrank ℝ (GeneratorSpace N))

def basis (N : ℕ) : OrthonormalBasis (GeneratorIndex N) ℝ (GeneratorSpace N) :=
  stdOrthonormalBasis ℝ (GeneratorSpace N)

def matrixInclusion (N : ℕ) : GeneratorSpace N →ₗ[ℝ] Algebra N :=
  (matrixMap N).restrictScalars ℝ |>.comp (hermitianTraceless N).subtype

theorem matrixInclusion_injective (N : ℕ) :
    Function.Injective (matrixInclusion N) :=
  (matrixMap_injective N).comp Subtype.val_injective

/-- Every Hermitian traceless operation on the original carrier is retained. -/
def ofMatrix (N : ℕ) (X : Algebra N) (hX : X.IsHermitian)
    (htr : Matrix.trace X = 0) : GeneratorSpace N :=
  ⟨matrixCoefficients N X, hX, htr⟩

@[simp] theorem matrixInclusion_ofMatrix (N : ℕ) (X : Algebra N)
    (hX : X.IsHermitian) (htr : Matrix.trace X = 0) :
    matrixInclusion N (ofMatrix N X hX htr) = X := rfl

def generator (N : ℕ) (a : GeneratorIndex N) : Algebra N :=
  matrixInclusion N (basis N a)

theorem generator_hermitian (N : ℕ) (a : GeneratorIndex N) :
    (generator N a).IsHermitian := (basis N a).property.1

theorem generator_trace (N : ℕ) (a : GeneratorIndex N) :
    Matrix.trace (generator N a) = 0 := (basis N a).property.2

theorem generator_real_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (generator N) :=
  (basis N).toBasis.linearIndependent.map' (matrixInclusion N)
    (LinearMap.ker_eq_bot.mpr (matrixInclusion_injective N))

def coefficients (N : ℕ) (X : GeneratorSpace N) : GeneratorIndex N → ℝ :=
  fun a => (basis N).repr X a

theorem real_expansion (N : ℕ) (X : GeneratorSpace N) :
    (∑ a, coefficients N X a • generator N a) = matrixInclusion N X := by
  have h := congrArg (matrixInclusion N) ((basis N).sum_repr X)
  simpa only [map_sum, map_smul, coefficients, generator] using h

theorem real_expansion_unique (N : ℕ) (X : GeneratorSpace N)
    (c : GeneratorIndex N → ℝ)
    (hc : (∑ a, c a • generator N a) = matrixInclusion N X) :
    c = coefficients N X := by
  have he : (∑ a, c a • basis N a) = X := by
    apply matrixInclusion_injective N
    simpa only [map_sum, map_smul, generator] using hc
  have h := congrArg (fun x : GeneratorSpace N => (basis N).repr x) he
  funext a
  simpa [coefficients, Pi.single_apply] using congrArg (fun x => x a) h

def representedGenerator (N : ℕ) (a : GeneratorIndex N) :
    Module.End ℂ (Space N) := action N (generator N a)

theorem representedGenerator_adjoint (N : ℕ) (a : GeneratorIndex N) :
    (representedGenerator N a).adjoint = representedGenerator N a := by
  rw [representedGenerator, HistoryCliffordAction.action_adjoint,
    (generator_hermitian N a).eq]

theorem representedGenerator_real_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (representedGenerator N) :=
  (generator_real_linearIndependent N).map' ((action N).toLinearMap.restrictScalars ℝ)
    (LinearMap.ker_eq_bot.mpr (action N).injective)

/-- The inner product is the full real trace pairing on the original
matrices. All off-diagonal coefficients occur in this identity. -/
theorem trace_metric (N : ℕ) (X Y : GeneratorSpace N) :
    (Matrix.trace ((matrixInclusion N X).conjTranspose * matrixInclusion N Y)).re =
      inner ℝ X Y := by
  change (∑ i, ∑ j, star (X.val (j, i)) * Y.val (j, i)).re = _
  rw [Finset.sum_comm]
  change (∑ i, ∑ j, star (X.val (i, j)) * Y.val (i, j)).re = _
  have hs := Fintype.sum_prod_type (fun a : Index N × Index N =>
    star (X.val a) * Y.val a)
  rw [← hs]
  rw [(hermitianTraceless N).coe_inner, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (star (X.val a) * Y.val a).re =
    (Inner.rclikeToReal ℂ ℂ).inner (X.val a) (Y.val a)
  rw [real_inner_eq_re_inner ℂ]
  change (star (X.val a) * Y.val a).re = (Y.val a * star (X.val a)).re
  rw [mul_comm]

theorem generator_trace_pair (N : ℕ) (a b : GeneratorIndex N) :
    (Matrix.trace ((generator N a).conjTranspose * generator N b)).re =
      if a = b then 1 else 0 := by
  rw [generator, generator, trace_metric]
  exact orthonormal_iff_ite.mp (basis N).orthonormal a b

theorem coefficients_trace (N : ℕ) (X : GeneratorSpace N) (a : GeneratorIndex N) :
    coefficients N X a =
      (Matrix.trace ((generator N a).conjTranspose * matrixInclusion N X)).re := by
  rw [coefficients, OrthonormalBasis.repr_apply_apply]
  exact (trace_metric N (basis N a) X).symm

theorem coefficients_parseval (N : ℕ) (X : GeneratorSpace N) :
    (∑ a, coefficients N X a ^ 2) =
      (Matrix.trace ((matrixInclusion N X).conjTranspose * matrixInclusion N X)).re := by
  simp only [coefficients, OrthonormalBasis.repr_apply_apply]
  rw [OrthonormalBasis.sum_sq_inner_right, trace_metric, real_inner_self_eq_norm_sq]

/-- The complete complex trace pairing of two Hermitian operations is real;
the real metric therefore determines it without discarding an imaginary part. -/
theorem trace_pair_real (N : ℕ) (X Y : GeneratorSpace N) :
    star (Matrix.trace (matrixInclusion N X * matrixInclusion N Y)) =
      Matrix.trace (matrixInclusion N X * matrixInclusion N Y) := by
  have hx : (matrixInclusion N X).conjTranspose = matrixInclusion N X := X.property.1.eq
  have hy : (matrixInclusion N Y).conjTranspose = matrixInclusion N Y := Y.property.1.eq
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    hx, hy, Matrix.trace_mul_comm]

theorem generator_complex_trace_pair (N : ℕ) (a b : GeneratorIndex N) :
    Matrix.trace (generator N a * generator N b) = if a = b then 1 else 0 := by
  have hr := generator_trace_pair N a b
  rw [(generator_hermitian N a).eq] at hr
  have hs := trace_pair_real N (basis N a) (basis N b)
  change star (Matrix.trace (generator N a * generator N b)) = _ at hs
  apply Complex.ext
  · split_ifs at * <;> simpa using hr
  · have hi := congrArg Complex.im hs
    change -(Matrix.trace (generator N a * generator N b)).im =
      (Matrix.trace (generator N a * generator N b)).im at hi
    simp only [apply_ite, Complex.one_im, Complex.zero_im, ite_self]
    linarith

theorem generator_complex_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (generator N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have ht := congrArg (fun X : Algebra N => Matrix.trace (generator N a * X)) hc
  simpa [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    generator_complex_trace_pair, Matrix.mul_zero, Matrix.trace_zero,
    smul_eq_mul, mul_ite, mul_one, mul_zero, eq_comm] using ht

theorem hermitian_matrix_expansion (N : ℕ) (X : Algebra N)
    (hX : X.IsHermitian) (htr : Matrix.trace X = 0) :
    (∑ a, (Matrix.trace ((generator N a).conjTranspose * X)).re • generator N a) = X := by
  simpa only [coefficients_trace, matrixInclusion_ofMatrix] using
    real_expansion N (ofMatrix N X hX htr)

def complexCoefficient (N : ℕ) (X : Algebra N) (a : GeneratorIndex N) : ℂ :=
  Matrix.trace (generator N a * X)

def complexReconstruction (N : ℕ) : Algebra N →ₗ[ℂ] Algebra N where
  toFun X := ∑ a, complexCoefficient N X a • generator N a
  map_add' X Y := by
    simp [complexCoefficient, Matrix.mul_add, Matrix.trace_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    simp [complexCoefficient, Matrix.trace_smul,
      smul_smul, Finset.smul_sum]

theorem complexReconstruction_hermitian (N : ℕ) (X : Algebra N)
    (hX : X.IsHermitian) (htr : Matrix.trace X = 0) :
    complexReconstruction N X = X := by
  have he (a : GeneratorIndex N) : (complexCoefficient N X a).im = 0 := by
    have hs := congrArg Complex.im (trace_pair_real N (basis N a) (ofMatrix N X hX htr))
    change -(complexCoefficient N X a).im = (complexCoefficient N X a).im at hs
    linarith
  have hc (a : GeneratorIndex N) : complexCoefficient N X a =
      ((Matrix.trace ((generator N a).conjTranspose * X)).re : ℂ) := by
    rw [(generator_hermitian N a).eq]
    apply Complex.ext
    · rfl
    · simpa only [complexCoefficient, Complex.ofReal_im] using he a
  change (∑ a, complexCoefficient N X a • generator N a) = X
  simp_rw [hc, Complex.coe_smul]
  exact hermitian_matrix_expansion N X hX htr

/-- Complexification of the actual real Hermitian basis covers the entire
traceless operation algebra. Both Hermitian parts are reconstructed first. -/
theorem complex_expansion (N : ℕ) (X : Algebra N) (htr : Matrix.trace X = 0) :
    (∑ a, complexCoefficient N X a • generator N a) = X := by
  have hxstar : Matrix.trace X.conjTranspose = 0 := by
    rw [Matrix.trace_conjTranspose, htr, star_zero]
  have hplus : (X + X.conjTranspose).IsHermitian := by
    change (X + X.conjTranspose).conjTranspose = _
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  have hminus : (Complex.I • (X - X.conjTranspose)).IsHermitian := by
    change (Complex.I • (X - X.conjTranspose)).conjTranspose = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I, sub_eq_add_neg,
      smul_add, smul_neg, neg_smul, neg_neg]
    abel
  have hp := complexReconstruction_hermitian N (X + X.conjTranspose) hplus
    (by rw [Matrix.trace_add, htr, hxstar, add_zero])
  have hm := complexReconstruction_hermitian N (Complex.I • (X - X.conjTranspose)) hminus
    (by rw [Matrix.trace_smul, Matrix.trace_sub, htr, hxstar, sub_self, smul_zero])
  rw [map_add] at hp
  rw [map_smul, map_sub] at hm
  have hd := congrArg (fun Y : Algebra N => (-Complex.I) • Y) hm
  simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at hd
  change complexReconstruction N X = X
  ext i j
  have hpi := congrArg (fun Y : Algebra N => Y i j) hp
  have hdi := congrArg (fun Y : Algebra N => Y i j) hd
  change complexReconstruction N X i j + complexReconstruction N X.conjTranspose i j =
    X i j + X.conjTranspose i j at hpi
  change complexReconstruction N X i j - complexReconstruction N X.conjTranspose i j =
    X i j - X.conjTranspose i j at hdi
  linear_combination (1 / 2 : ℂ) * hpi + (1 / 2 : ℂ) * hdi

theorem complex_expansion_unique (N : ℕ) (X : Algebra N)
    (htr : Matrix.trace X = 0) (c : GeneratorIndex N → ℂ)
    (hc : (∑ a, c a • generator N a) = X) : c = complexCoefficient N X := by
  apply (generator_complex_linearIndependent N).fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply] using hc.trans (complex_expansion N X htr).symm

/-- The independent Hermitian generators give coordinates for the entire
complex traceless algebra, not only for its real Hermitian part. -/
def complexCoordinateMap (N : ℕ) : HistoryTracelessCoordinates.traceless N →ₗ[ℂ]
    (GeneratorIndex N → ℂ) where
  toFun X := complexCoefficient N X.val
  map_add' X Y := by
    funext a
    simp [complexCoefficient, Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    funext a
    simp [complexCoefficient, Matrix.trace_smul]

theorem complexCoordinateMap_bijective (N : ℕ) :
    Function.Bijective (complexCoordinateMap N) := by
  constructor
  · intro X Y h
    apply Subtype.ext
    calc
      X.val = ∑ a, complexCoefficient N X.val a • generator N a :=
        (complex_expansion N X.val X.property).symm
      _ = ∑ a, complexCoefficient N Y.val a • generator N a := by
        change complexCoefficient N X.val = complexCoefficient N Y.val at h
        rw [h]
      _ = Y.val := complex_expansion N Y.val Y.property
  · intro c
    let X : Algebra N := ∑ a, c a • generator N a
    have hx : Matrix.trace X = 0 := by
      simp [X, Matrix.trace_sum, Matrix.trace_smul, generator_trace]
    refine ⟨⟨X, hx⟩, ?_⟩
    exact (complex_expansion_unique N X hx c rfl).symm

def complexCoordinateEquiv (N : ℕ) : HistoryTracelessCoordinates.traceless N ≃ₗ[ℂ]
    (GeneratorIndex N → ℂ) :=
  LinearEquiv.ofBijective (complexCoordinateMap N) (complexCoordinateMap_bijective N)

theorem generator_count (N : ℕ) :
    Fintype.card (GeneratorIndex N) = HistoryAdjointCasimir.dimension N ^ 2 - 1 := by
  have h₁ := (complexCoordinateEquiv N).finrank_eq
  have h₂ := (HistoryTracelessCoordinates.coordinateEquiv N).finrank_eq
  simp only [Module.finrank_pi] at h₁ h₂
  change Module.finrank ℂ (HistoryTracelessCoordinates.traceless N) =
    Fintype.card (HistoryTracelessCoordinates.CoordinateIndex N) at h₂
  rw [← h₁, h₂, HistoryTracelessCoordinates.coordinate_count]

def lieGenerator (N : ℕ) (a : GeneratorIndex N) : Algebra N :=
  Complex.I • generator N a

theorem lieGenerator_skewHermitian (N : ℕ) (a : GeneratorIndex N) :
    (lieGenerator N a).conjTranspose = -lieGenerator N a := by
  simp [lieGenerator, Matrix.conjTranspose_smul, (generator_hermitian N a).eq,
    Complex.conj_I]

theorem lieGenerator_trace (N : ℕ) (a : GeneratorIndex N) :
    Matrix.trace (lieGenerator N a) = 0 := by
  simp [lieGenerator, Matrix.trace_smul, generator_trace]

theorem complexCoefficient_real (N : ℕ) (X : Algebra N) (hX : X.IsHermitian)
    (a : GeneratorIndex N) : (complexCoefficient N X a).im = 0 := by
  have hs : star (Matrix.trace (generator N a * X)) =
      Matrix.trace (generator N a * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hX.eq, (generator_hermitian N a).eq, Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hs
  change -(complexCoefficient N X a).im = (complexCoefficient N X a).im at hi
  linarith

structure Conclusions : Prop where
  actual_hermitian_generators : ∀ N a, (generator N a).IsHermitian
  all_traces_zero : ∀ N a, Matrix.trace (generator N a) = 0
  real_independence : ∀ N, LinearIndependent ℝ (generator N)
  complete_expansion : ∀ N X,
    (∑ a, coefficients N X a • generator N a) = matrixInclusion N X
  unique_real_coefficients : ∀ N X c,
    (∑ a, c a • generator N a) = matrixInclusion N X → c = coefficients N X
  full_metric : ∀ N X Y,
    (Matrix.trace ((matrixInclusion N X).conjTranspose * matrixInclusion N Y)).re =
      inner ℝ X Y
  complex_independence : ∀ N, LinearIndependent ℂ (generator N)
  complete_complex_expansion : ∀ N X, Matrix.trace X = 0 →
    (∑ a, complexCoefficient N X a • generator N a) = X
  unique_complex_coefficients : ∀ N X c, Matrix.trace X = 0 →
    (∑ a, c a • generator N a) = X → c = complexCoefficient N X
  full_parseval_metric : ∀ N X, (∑ a, coefficients N X a ^ 2) =
    (Matrix.trace ((matrixInclusion N X).conjTranspose * matrixInclusion N X)).re
  intrinsic_generator_count : ∀ N,
    Fintype.card (GeneratorIndex N) = HistoryAdjointCasimir.dimension N ^ 2 - 1

theorem generated : Conclusions where
  actual_hermitian_generators := generator_hermitian
  all_traces_zero := generator_trace
  real_independence := generator_real_linearIndependent
  complete_expansion := real_expansion
  unique_real_coefficients := real_expansion_unique
  full_metric := trace_metric
  complex_independence := generator_complex_linearIndependent
  complete_complex_expansion := complex_expansion
  unique_complex_coefficients := fun N X c htr hc => complex_expansion_unique N X htr c hc
  full_parseval_metric := coefficients_parseval
  intrinsic_generator_count := generator_count

end GeneratedFoundations.Arithmetic.HistoryHermitianBasis
