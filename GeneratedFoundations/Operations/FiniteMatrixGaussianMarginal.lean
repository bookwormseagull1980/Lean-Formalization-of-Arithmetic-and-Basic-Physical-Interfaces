module

public import GeneratedFoundations.Operations.FiniteMatrixGaussianVariation
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Unique retained states of the full Gaussian source

The observation map selects the original coordinates. Its covariance is
the corresponding submatrix of the full inverse precision, rather than
the inverse of a prematurely truncated precision. Inverting that retained
covariance gives the unique positive effective precision and its unique
centred Gaussian law. Successive restrictions compose exactly.

The two-block identity identifies this precision with the full Schur
complement. No vanishing cross block is imposed.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Operations.FiniteMatrixGaussian

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq η]

def select (e : κ → ι) : Space ι →L[ℝ] Space κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => x (e i)
      map_add' := fun x y => by ext i; rfl
      map_smul' := fun c x => by ext i; rfl }

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem select_apply (e : κ → ι) (x : Space ι) (i : κ) :
    select e x i = x (e i) := rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq η] in
theorem select_comp (e : κ → ι) (f : η → κ) :
    (select f).comp (select e) = select (e ∘ f) := by
  ext x i
  rfl

def retainedCovariance (P : Matrix ι ι ℝ) (e : κ → ι) : Matrix κ κ ℝ :=
  P⁻¹.submatrix e e

def retainedPrecision (P : Matrix ι ι ℝ) (e : κ → ι) : Matrix κ κ ℝ :=
  (retainedCovariance P e)⁻¹

omit [Fintype κ] [DecidableEq κ] in
theorem retainedCovariance_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) : (retainedCovariance P e).PosDef :=
  hP.inv.submatrix he

theorem retainedPrecision_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) : (retainedPrecision P e).PosDef :=
  (retainedCovariance_posDef hP he).inv

theorem retainedPrecision_inverse {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) :
    (retainedPrecision P e)⁻¹ = retainedCovariance P e := by
  let : Invertible (retainedCovariance P e) :=
    Classical.choice (retainedCovariance_posDef hP he).isUnit.nonempty_invertible
  exact Matrix.inv_inv_of_invertible (A := retainedCovariance P e)

omit [DecidableEq κ] in
theorem selected_mean (P : Matrix ι ι ℝ) (e : κ → ι) :
    (∫ x, x ∂(law P).map (select e)) = 0 := by
  rw [ContinuousLinearMap.integral_id_map, mean_zero, map_zero]
  exact IsGaussian.integrable_id

omit [DecidableEq κ] in
theorem selected_covariance {P : Matrix ι ι ℝ} (hP : P.PosDef) (e : κ → ι) :
    FinitePrecisionGaussian.coordinateCovariance ((law P).map (select e)) =
      retainedCovariance P e := by
  ext i j
  change cov[fun x : Space κ => x i, fun x : Space κ => x j;
    (law P).map (select e)] = P⁻¹ (e i) (e j)
  rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  change cov[fun x : Space ι => x (e i), fun x : Space ι => x (e j); law P] = _
  exact congrFun (congrFun (coordinateCovariance_eq hP) (e i)) (e j)

/-- The retained law is an actual marginal of the same complete source. -/
theorem selected_law {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) :
    (law P).map (select e) = law (retainedPrecision P e) := by
  apply law_unique (retainedPrecision_posDef hP he)
  · exact selected_mean P e
  · rw [selected_covariance hP]
    exact inverse_mul_precision (retainedCovariance_posDef hP he)

theorem retained_law_existsUnique {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) :
    ∃! ν : Measure (Space κ), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      retainedPrecision P e * FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  law_existsUnique (retainedPrecision_posDef hP he)

theorem selected_score_mean {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) (V : Matrix κ κ ℝ) :
    (∫ x, score V (select e x) ∂law P) =
      Matrix.trace (retainedCovariance P e * V) / 2 := by
  calc
    (∫ x, score V (select e x) ∂law P) =
        ∫ y, score V y ∂(law P).map (select e) :=
      (integral_map (by fun_prop) (by unfold score; fun_prop)).symm
    _ = _ := by
      rw [selected_law hP he, score_mean_trace (retainedPrecision_posDef hP he),
        retainedPrecision_inverse hP he]

theorem selected_score_covariance {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) (V W : Matrix κ κ ℝ) (hW : W.IsSymm) :
    cov[fun x => score V (select e x), fun x => score W (select e x); law P] =
      Matrix.trace (retainedCovariance P e * V * retainedCovariance P e * W) / 2 := by
  have hm := covariance_map (μ := law P) (Z := select e)
    (X := score V) (Y := score W) (by unfold score; fun_prop)
    (by unfold score; fun_prop) (by fun_prop)
  calc
    cov[fun x => score V (select e x), fun x => score W (select e x); law P] =
        cov[score V, score W; (law P).map (select e)] := by
      simpa only [Function.comp_def] using! hm.symm
    _ = _ := by
      rw [selected_law hP he,
        score_covariance_trace (retainedPrecision_posDef hP he) V W hW,
        retainedPrecision_inverse hP he]

theorem retainedPrecision_comp {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {e : κ → ι} (he : Function.Injective e) (f : η → κ) :
    retainedPrecision (retainedPrecision P e) f = retainedPrecision P (e ∘ f) := by
  change (((retainedPrecision P e)⁻¹).submatrix f f)⁻¹ =
    retainedPrecision P (e ∘ f)
  rw [retainedPrecision_inverse hP he]
  rfl

omit [DecidableEq κ] [DecidableEq η] in
/-- Elimination in stages preserves the whole marginal law, including
every correlation already carried by the full source covariance. -/
theorem selected_law_comp (P : Matrix ι ι ℝ) (e : κ → ι) (f : η → κ) :
    ((law P).map (select e)).map (select f) = (law P).map (select (e ∘ f)) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The exact two-block effective precision. Both mixed blocks survive. -/
theorem retainedPrecision_fromBlocks {P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hP : P.PosDef) :
    retainedPrecision P Sum.inl =
      P.toBlocks₁₁ - P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹ * P.toBlocks₂₁ := by
  let C := P⁻¹
  have hC : (C.toBlocks₁₁).PosDef := hP.inv.submatrix Sum.inl_injective
  have hD : (P.toBlocks₂₂).PosDef := hP.submatrix Sum.inr_injective
  have htop : P.toBlocks₁₁ * C.toBlocks₁₁ + P.toBlocks₁₂ * C.toBlocks₂₁ = 1 := by
    have h := precision_mul_inverse hP
    change P * C = 1 at h
    rw [← P.fromBlocks_toBlocks, ← C.fromBlocks_toBlocks, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] at h
    exact congrArg Matrix.toBlocks₁₁ h
  have hbottom : P.toBlocks₂₁ * C.toBlocks₁₁ + P.toBlocks₂₂ * C.toBlocks₂₁ = 0 := by
    have h := precision_mul_inverse hP
    change P * C = 1 at h
    rw [← P.fromBlocks_toBlocks, ← C.fromBlocks_toBlocks, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] at h
    exact congrArg Matrix.toBlocks₂₁ h
  have hm : C.toBlocks₂₁ = -(P.toBlocks₂₂)⁻¹ * P.toBlocks₂₁ * C.toBlocks₁₁ := by
    have h := congrArg (fun M => (P.toBlocks₂₂)⁻¹ * M) hbottom
    simp only [Matrix.mul_add, Matrix.mul_zero] at h
    rw [← Matrix.mul_assoc (P.toBlocks₂₂)⁻¹ P.toBlocks₂₂,
      inverse_mul_precision hD, Matrix.one_mul] at h
    have he := eq_neg_of_add_eq_zero_right h
    simpa only [Matrix.neg_mul, Matrix.mul_assoc] using he
  have hs : (P.toBlocks₁₁ - P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹ * P.toBlocks₂₁) *
      C.toBlocks₁₁ = 1 := by
    rw [hm] at htop
    simpa only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg,
      Matrix.mul_assoc] using htop
  have h := congrArg (fun M => M * (C.toBlocks₁₁)⁻¹) hs
  rw [Matrix.mul_assoc, precision_mul_inverse hC, Matrix.mul_one, Matrix.one_mul] at h
  exact h.symm

end GeneratedFoundations.Operations.FiniteMatrixGaussian
