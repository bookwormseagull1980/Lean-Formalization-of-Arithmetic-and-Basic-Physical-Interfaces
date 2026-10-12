module

public import GeneratedFoundations.Arithmetic.ReducedExpressionFibers
public import GeneratedFoundations.Arithmetic.GeneratedTransport

/-!
# Generated realization and transport of reduced expressions

Reduced expressions are realized on the actual typed source endomorphisms
already constructed from minimal change.  Their realization commutes with the
canonical comparison of scales and orientations.  The expression object is
not enlarged and no spectral label, weighting, or comparison map is chosen.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Source
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Spectral
open scoped NNReal

namespace GeneratedFoundations.Arithmetic.ReducedExpression

open NativeModes TypedSourceModes

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable (L : ℝ) [Fact (0 < L)] (o : OrientationOnCarrier d)

/-- The canonical equivalence from native modes to the actual typed source
endomorphisms. -/
def nativeToTyped : NativeModes.Mode ≃+* Mode d h L o :=
  (GeneratedModes.nativeEquiv L).symm.trans (generatedEquiv d h L o).symm

/-- The six-law comparison target on the actual typed source maps. -/
def typedTarget : Target (Mode d h L o) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_zero_right := add_zero
  add_zero_left := zero_add
  mul_one_right := mul_one
  mul_one_left := one_mul
  mul_zero_right := mul_zero
  mul_zero_left := zero_mul

/-- Evaluation of a reduced expression as an actual source endomorphism. -/
def evalTyped : Expr → Mode d h L o := Target.interpret (typedTarget d h L o)

private def typedEvaluationFromNative : Target.Hom (typedTarget d h L o) where
  toFun e := nativeToTyped d h L o (evalNative e)
  map_zero := by simp [nativeToTyped, typedTarget]
  map_one := by simp [nativeToTyped, typedTarget]
  map_add e f := by simp [nativeToTyped, typedTarget]
  map_mul e f := by simp [nativeToTyped, typedTarget]

/-- Typed evaluation is precisely the canonical image of native evaluation. -/
theorem evalTyped_eq_nativeToTyped (e : Expr) :
    evalTyped d h L o e = nativeToTyped d h L o (evalNative e) := by
  have heq := congrArg (fun F : Target.Hom (typedTarget d h L o) => F e)
    (Target.hom_unique (Target.canonicalHom (typedTarget d h L o))
      (typedEvaluationFromNative d h L o))
  exact heq

@[simp] theorem evalTyped_zero : evalTyped d h L o 0 = 0 := rfl
@[simp] theorem evalTyped_one : evalTyped d h L o 1 = 1 := rfl

@[simp] theorem evalTyped_add (e f : Expr) :
    evalTyped d h L o (e + f) = evalTyped d h L o e + evalTyped d h L o f :=
  (Target.canonicalHom (typedTarget d h L o)).map_add e f

@[simp] theorem evalTyped_mul (e f : Expr) :
    evalTyped d h L o (e * f) = evalTyped d h L o e * evalTyped d h L o f :=
  (Target.canonicalHom (typedTarget d h L o)).map_mul e f

theorem evalTyped_surjective : Function.Surjective (evalTyped d h L o) := by
  intro u
  obtain ⟨v, rfl⟩ := (nativeToTyped d h L o).surjective u
  obtain ⟨e, rfl⟩ := evalNative_surjective v
  exact ⟨e, evalTyped_eq_nativeToTyped d h L o e⟩

/-- Every actual generated source mode has a finite reduced-expression fiber. -/
theorem finite_typed_fiber (u : Mode d h L o) :
    Set.Finite {e : Expr | evalTyped d h L o e = u} := by
  have hset : {e : Expr | evalTyped d h L o e = u} =
      {e : Expr | evalNat e = NativeModes.index ((nativeToTyped d h L o).symm u)} := by
    ext e
    simp only [Set.mem_ofPred_eq, evalTyped_eq_nativeToTyped,
      evalNative_eq_powerMode_evalNat]
    constructor
    · intro he
      have hn := congrArg (nativeToTyped d h L o).symm he
      simp only [RingEquiv.symm_apply_apply] at hn
      rw [← NativeModes.powerMode_index ((nativeToTyped d h L o).symm u)] at hn
      exact NativeModes.powerMode_injective hn
    · intro he
      rw [he, NativeModes.powerMode_index]
      exact (nativeToTyped d h L o).apply_symm_apply u
  rw [hset]
  exact finite_fiber _

/-- The generated Gaussian response is constant on each expression-evaluation
fiber.  This is a scalar compatibility statement, not an additional dynamics
on the fiber. -/
theorem gaussianResponse_constant_on_fiber {x y : Expr}
    (hxy : evalNat x = evalNat y) (t : ℝ≥0) :
    NeumannSpectralProjections.response L
        (GeneratedTransport.component d h L o (evalTyped d h L o x)) t =
      NeumannSpectralProjections.response L
        (GeneratedTransport.component d h L o (evalTyped d h L o y)) t := by
  have hn : evalNative x = evalNative y := by
    rw [evalNative_eq_powerMode_evalNat, evalNative_eq_powerMode_evalNat, hxy]
  have ht : evalTyped d h L o x = evalTyped d h L o y := by
    rw [evalTyped_eq_nativeToTyped, evalTyped_eq_nativeToTyped, hn]
  rw [ht]

variable (e : MinimalCarrier.OrthogonalChangeDatum) (he : MinimalCarrier.IsMinimal e)
variable (M : ℝ) [Fact (0 < M)] (p : OrientationOnCarrier e)

private def transportedTypedEvaluation : Target.Hom (typedTarget e he M p) where
  toFun x := GeneratedTransport.transport d h L o e he M p (evalTyped d h L o x)
  map_zero := by simp [typedTarget]
  map_one := by simp [typedTarget]
  map_add x y := by simp [typedTarget]
  map_mul x y := by simp [typedTarget]

/-- Expression evaluation commutes with the previously derived canonical
scale-and-orientation transport. -/
theorem evalTyped_transport (x : Expr) :
    GeneratedTransport.transport d h L o e he M p (evalTyped d h L o x) =
      evalTyped e he M p x := by
  have heq := congrArg (fun F : Target.Hom (typedTarget e he M p) => F x)
    (Target.hom_unique (transportedTypedEvaluation d h L o e he M p)
      (Target.canonicalHom (typedTarget e he M p)))
  exact heq

end GeneratedFoundations.Arithmetic.ReducedExpression
