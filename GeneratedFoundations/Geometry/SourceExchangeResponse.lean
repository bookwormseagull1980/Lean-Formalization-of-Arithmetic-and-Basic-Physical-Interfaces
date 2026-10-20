module

public import GeneratedFoundations.Geometry.SourceScalarResponse
public import GeneratedFoundations.Geometry.SourcePreExchangeResponse
public import GeneratedFoundations.Geometry.SourceQuadraticSplit
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Unitary resolution of the common source exchange sectors

The source tensor square is resolved by its actual orthogonal symmetric
and alternating spaces. Tensor distribution preserves the complete inner
product. Conjugation therefore transports arbitrary full endomorphisms and
their adjoints, including operators mixing the resolved sectors.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open GeneratedFoundations.Geometry.SourceQuadraticSplit
open GeneratedFoundations.Geometry.SourceJointResponse (W L S Coloured Scalar sourceOperator)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Operations.ReversalRealConnector (Spinor)

namespace GeneratedFoundations.Geometry.SourceExchangeResponse

abbrev ResponseSpace := WithLp 2 (Coloured × Scalar)

def responseCoordinates : (Coloured × Scalar) ≃ₗ[ℂ] ResponseSpace :=
  (WithLp.linearEquiv 2 ℂ (Coloured × Scalar)).symm

def spinOnResponse : Module.End ℂ S →ₐ[ℂ] Module.End ℂ ResponseSpace :=
  ((responseCoordinates.conjAlgEquiv ℂ).toAlgHom.comp
    (LinearMap.prodMapAlgHom ℂ Coloured Scalar)).comp
      SourceJointResponse.spinResponse

@[simp] theorem spinOnResponse_apply (h : Module.End ℂ S) (x : ResponseSpace) :
    WithLp.ofLp (spinOnResponse h x) =
      (TensorProduct.map 1 h (WithLp.ofLp x).1,
        TensorProduct.map 1 h (WithLp.ofLp x).2) := rfl

abbrev C := SourcePreExchangeResponse.C
abbrev FullCarrier := SourcePreExchangeResponse.FullCarrier
abbrev SplitColour := WithLp 2 (W × L)

instance splitTensorNormed : NormedAddCommGroup (SplitColour ⊗[ℂ] S) :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := SplitColour) (F := S)

instance splitTensorInner : InnerProductSpace ℂ (SplitColour ⊗[ℂ] S) :=
  TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := SplitColour) (F := S)

theorem symm_apply_of_apply_eq {E F : Type*}
    (e : E ≃ F) (x : F) (y : E) (h : e y = x) : e.symm x = y :=
  (congrArg e.symm h.symm).trans (e.symm_apply_apply y)

/-- The normalized source eigenspaces, with their actual orthogonal inverse sum. -/
def colourSplit : C ≃ₗᵢ[ℂ] SplitColour :=
  orthogonalSum.symm.trans
    (LinearIsometryEquiv.withLpProdCongr 2 symmetricUnitary alternatingUnitary)

theorem colourSplit_apply (c : C) :
    WithLp.ofLp (colourSplit c) =
      (symmetricUnitary (WithLp.ofLp (orthogonalSum.symm c)).1,
        alternatingUnitary (WithLp.ofLp (orthogonalSum.symm c)).2) := rfl

theorem colourSplit_symmetric (c : symmetricSpace) :
    colourSplit (c : C) = WithLp.toLp 2 (symmetricUnitary c, 0) := by
  have hc : orthogonalSum.symm (c : C) = WithLp.toLp 2 (c, 0) := by
    apply symm_apply_of_apply_eq orthogonalSum.toEquiv
    change sumEquiv (c, 0) = (c : C)
    exact (sumEquiv_apply c 0).trans (add_zero _)
  apply WithLp.ofLp_injective 2
  exact (colourSplit_apply (c : C)).trans
    ((congrArg (fun p : WithLp 2 (symmetricSpace × alternatingSpace) =>
      (symmetricUnitary (WithLp.ofLp p).1, alternatingUnitary (WithLp.ofLp p).2)) hc).trans
      (congrArg (fun l : L => (symmetricUnitary c, l)) (map_zero alternatingUnitary)))

theorem colourSplit_alternating (c : alternatingSpace) :
    colourSplit (c : C) = WithLp.toLp 2 (0, alternatingUnitary c) := by
  have hc : orthogonalSum.symm (c : C) = WithLp.toLp 2 (0, c) := by
    apply symm_apply_of_apply_eq orthogonalSum.toEquiv
    change sumEquiv (0, c) = (c : C)
    exact (sumEquiv_apply 0 c).trans (zero_add _)
  apply WithLp.ofLp_injective 2
  exact (colourSplit_apply (c : C)).trans
    ((congrArg (fun p : WithLp 2 (symmetricSpace × alternatingSpace) =>
      (symmetricUnitary (WithLp.ofLp p).1, alternatingUnitary (WithLp.ofLp p).2)) hc).trans
      (congrArg (fun w : W => (w, alternatingUnitary c)) (map_zero symmetricUnitary)))

/-- Algebraic tensor distribution, with the `L²` sum on both ends. -/
def splitTensorLinear : SplitColour ⊗[ℂ] S ≃ₗ[ℂ] ResponseSpace :=
  (TensorProduct.congr (WithLp.linearEquiv 2 ℂ (W × L)) (LinearEquiv.refl ℂ S)).trans
    ((TensorProduct.prodLeft ℂ ℂ W L S).trans
      responseCoordinates)

@[simp] theorem splitTensorLinear_tmul (c : SplitColour) (s : S) :
    WithLp.ofLp (splitTensorLinear (c ⊗ₜ[ℂ] s)) =
      ((WithLp.ofLp c).1 ⊗ₜ[ℂ] s, (WithLp.ofLp c).2 ⊗ₜ[ℂ] s) := rfl

theorem splitTensorLinear_inner (x y : SplitColour ⊗[ℂ] S) :
    inner ℂ (splitTensorLinear x) (splitTensorLinear y) = inner ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul c s =>
      induction y using TensorProduct.inductionOn with
      | tmul d t =>
          simp only [WithLp.prod_inner_apply, splitTensorLinear_tmul,
            TensorProduct.inner_tmul, add_mul]
      | add y z hy hz => simp only [map_add, inner_add_right (𝕜 := ℂ), hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left (𝕜 := ℂ), hx, hz]

theorem norm_eq_of_inner_eq {E F : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
    (x : E) (y : F) (h : inner ℂ x x = inner ℂ y y) : ‖x‖ = ‖y‖ :=
  (norm_eq_sqrt_re_inner (𝕜 := ℂ) x).trans
    ((congrArg (fun z : ℂ => Real.sqrt z.re) h).trans
      (norm_eq_sqrt_re_inner (𝕜 := ℂ) y).symm)

def splitTensorUnitary : SplitColour ⊗[ℂ] S ≃ₗᵢ[ℂ] ResponseSpace where
  toLinearEquiv := splitTensorLinear
  norm_map' x := norm_eq_of_inner_eq (splitTensorLinear x) x (splitTensorLinear_inner x x)

/-- The actual source exchange split followed by tensor distribution. -/
def exchangeUnitary : FullCarrier ≃ₗᵢ[ℂ] ResponseSpace := by
  exact (TensorProduct.congrIsometry (𝕜 := ℂ) (E := C) (F := S)
    (G := SplitColour) (H := S) (by exact colourSplit) (LinearIsometryEquiv.refl ℂ S)).trans
    splitTensorUnitary

@[simp] theorem exchangeUnitary_tmul (c : C) (s : S) :
    WithLp.ofLp (exchangeUnitary (c ⊗ₜ[ℂ] s)) =
      ((WithLp.ofLp (colourSplit c)).1 ⊗ₜ[ℂ] s,
        (WithLp.ofLp (colourSplit c)).2 ⊗ₜ[ℂ] s) := by
  change WithLp.ofLp (splitTensorLinear
    (TensorProduct.congr colourSplit.toLinearEquiv (LinearEquiv.refl ℂ S)
      (c ⊗ₜ[ℂ] s))) = _
  simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, splitTensorLinear_tmul]
  rfl

theorem exchangeUnitary_symmetric_tmul (c : symmetricSpace) (s : S) :
    exchangeUnitary ((c : C) ⊗ₜ[ℂ] s) =
      WithLp.toLp 2 (symmetricUnitary c ⊗ₜ[ℂ] s, 0) := by
  apply WithLp.ofLp_injective 2
  simp [exchangeUnitary_tmul, colourSplit_symmetric]

theorem exchangeUnitary_alternating_tmul (c : alternatingSpace) (s : S) :
    exchangeUnitary ((c : C) ⊗ₜ[ℂ] s) =
      WithLp.toLp 2 (0, alternatingUnitary c ⊗ₜ[ℂ] s) := by
  apply WithLp.ofLp_injective 2
  simp [exchangeUnitary_tmul, colourSplit_alternating]

theorem exchangeUnitary_spinLift (h : Module.End ℂ S) (x : FullCarrier) :
    exchangeUnitary (SourcePreExchangeResponse.spinLift h x) =
      spinOnResponse h (exchangeUnitary x) := by
  have he : exchangeUnitary.toLinearEquiv.toLinearMap.comp
      (SourcePreExchangeResponse.spinLift h) =
      (spinOnResponse h).comp exchangeUnitary.toLinearEquiv.toLinearMap := by
    apply TensorProduct.ext'
    intro c s
    apply WithLp.ofLp_injective 2
    change WithLp.ofLp (exchangeUnitary (SourcePreExchangeResponse.spinLift h
      (c ⊗ₜ[ℂ] s))) =
      WithLp.ofLp (spinOnResponse h (exchangeUnitary (c ⊗ₜ[ℂ] s)))
    simp [SourcePreExchangeResponse.spinLift, TensorProduct.map_tmul,
      exchangeUnitary_tmul]
  exact LinearMap.congr_fun he x

def operatorTransport : Module.End ℂ FullCarrier ≃ₐ[ℂ] Module.End ℂ ResponseSpace :=
  exchangeUnitary.toLinearEquiv.conjAlgEquiv ℂ

@[simp] theorem operatorTransport_apply (T : Module.End ℂ FullCarrier) (y : ResponseSpace) :
    operatorTransport T y = exchangeUnitary (T (exchangeUnitary.symm y)) := rfl

theorem operatorTransport_adjoint (T : Module.End ℂ FullCarrier) :
    operatorTransport T.adjoint = (operatorTransport T).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (exchangeUnitary (T.adjoint (exchangeUnitary.symm x))) y =
    inner ℂ x (exchangeUnitary (T (exchangeUnitary.symm y)))
  rw [exchangeUnitary.inner_map_eq_flip, LinearMap.adjoint_inner_left]
  exact exchangeUnitary.symm.inner_map_eq_flip x (T (exchangeUnitary.symm y))

@[simp] theorem operatorTransport_spinLift (h : Module.End ℂ S) :
    operatorTransport (SourcePreExchangeResponse.spinLift h) =
      spinOnResponse h := by
  apply LinearMap.ext
  intro y
  change exchangeUnitary (SourcePreExchangeResponse.spinLift h (exchangeUnitary.symm y)) =
    spinOnResponse h y
  exact (exchangeUnitary_spinLift h (exchangeUnitary.symm y)).trans
    (congrArg (spinOnResponse h) (exchangeUnitary.apply_symm_apply y))

theorem operatorTransport_eq_spinOnSource_iff (T : Module.End ℂ FullCarrier)
    (h : Module.End ℂ S) :
    operatorTransport T = spinOnResponse h ↔
      T = SourcePreExchangeResponse.spinLift h := by
  constructor
  · intro he
    exact operatorTransport.injective (he.trans (operatorTransport_spinLift h).symm)
  · intro he
    exact (congrArg operatorTransport he).trans (operatorTransport_spinLift h)

theorem sourceNatural_iff_unique_transported_spinor (T : Module.End ℂ FullCarrier) :
    SourcePreExchangeResponse.SourceNatural T ↔
      ∃! h : Module.End ℂ S, operatorTransport T = spinOnResponse h := by
  simp_rw [operatorTransport_eq_spinOnSource_iff]
  exact SourcePreExchangeResponse.sourceNatural_iff_existsUnique_spinor T

/-- These are the transported independent pre-exchange responses, including
their possible mixing of the retained exchange sectors. -/
def SplitSourceNatural (A : Module.End ℂ ResponseSpace) : Prop :=
  (∀ U : SU2, A * operatorTransport (SourcePreExchangeResponse.colourAction
      (SourcePreExchangeResponse.leftResponse (sourceOperator 1 U))) =
    operatorTransport (SourcePreExchangeResponse.colourAction
      (SourcePreExchangeResponse.leftResponse (sourceOperator 1 U))) * A) ∧
  (∀ V : SU2, A * operatorTransport (SourcePreExchangeResponse.colourAction
      (SourcePreExchangeResponse.rightResponse (sourceOperator 1 V))) =
    operatorTransport (SourcePreExchangeResponse.colourAction
      (SourcePreExchangeResponse.rightResponse (sourceOperator 1 V))) * A)

theorem algebraEquiv_commutes_iff {A B : Type*}
    [Semiring A] [Algebra ℂ A] [Semiring B] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (x y : A) :
    e x * e y = e y * e x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff

theorem operatorTransport_commutes_iff (T A : Module.End ℂ FullCarrier) :
    operatorTransport T * operatorTransport A = operatorTransport A * operatorTransport T ↔
      T * A = A * T :=
  algebraEquiv_commutes_iff operatorTransport T A

theorem splitSourceNatural_operatorTransport (T : Module.End ℂ FullCarrier) :
    SplitSourceNatural (operatorTransport T) ↔ SourcePreExchangeResponse.SourceNatural T := by
  simp only [SplitSourceNatural, SourcePreExchangeResponse.SourceNatural,
    operatorTransport_commutes_iff]

theorem splitSourceNatural_iff_unique_spinor (A : Module.End ℂ ResponseSpace) :
    SplitSourceNatural A ↔
      ∃! h : Module.End ℂ S, A = spinOnResponse h := by
  simpa only [operatorTransport.apply_symm_apply] using
    (splitSourceNatural_operatorTransport (operatorTransport.symm A)).trans
      (sourceNatural_iff_unique_transported_spinor (operatorTransport.symm A))

/-- P6 reality is imposed on the unique reduced source spin map after transport. -/
def SplitElementary (A : Module.End ℂ ResponseSpace) : Prop :=
  SplitSourceNatural A ∧ ∀ h : Module.End ℂ S,
    A = spinOnResponse h → SourceScalarResponse.ReversalCompatible h

theorem splitElementary_operatorTransport (T : Module.End ℂ FullCarrier) :
    SplitElementary (operatorTransport T) ↔ SourceScalarResponse.Elementary T := by
  simp only [SplitElementary, SourceScalarResponse.Elementary,
    splitSourceNatural_operatorTransport, operatorTransport_eq_spinOnSource_iff]

theorem elementary_iff_unique_transported_doublet (T : Module.End ℂ FullCarrier) :
    SourceScalarResponse.Elementary T ↔ ∃! H : Spinor,
      operatorTransport T = spinOnResponse (SourceScalarResponse.doubletLift H) := by
  simp_rw [operatorTransport_eq_spinOnSource_iff]
  exact SourceScalarResponse.elementary_iff_unique_doublet T

theorem splitElementary_iff_unique_doublet (A : Module.End ℂ ResponseSpace) :
    SplitElementary A ↔ ∃! H : Spinor,
      A = spinOnResponse (SourceScalarResponse.doubletLift H) := by
  simpa only [operatorTransport.apply_symm_apply] using
    (splitElementary_operatorTransport (operatorTransport.symm A)).trans
      (elementary_iff_unique_transported_doublet (operatorTransport.symm A))

end GeneratedFoundations.Geometry.SourceExchangeResponse
