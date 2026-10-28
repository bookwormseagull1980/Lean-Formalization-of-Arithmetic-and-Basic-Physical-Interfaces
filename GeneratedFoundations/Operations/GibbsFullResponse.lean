module

public import GeneratedFoundations.Operations.GibbsConnectedResponse

/-!
# The connected response at every Hermitian observation

The reference log-intensity is fixed. A finite Hermitian observation need
not commute with it. Differentiating the same partition function twice and
transporting the result through the spectral theorem gives the complete
positive logarithmic-mean form at that observation. The only null direction
is the scalar matrix. No restriction to diagonal perturbations is made.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.GibbsFullResponse

open PreparedTraceForm (Mat Hermitian Traceless realTrace)
open GibbsExponentialDifferentiation (realDiagonal expDerivative)
open GibbsTraceDifferentiation (partition tracePair conjugation)
open GibbsConnectedResponse (response)

private theorem hasFDerivAt_clm_comp_dual
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] E →L[ℝ] ℝ) {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => L (f y)) (L.comp f') x :=
  L.hasFDerivAt.comp x hf

private theorem hasFDerivAt_smul_dual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → ℝ} {c' : E →L[ℝ] ℝ}
    {f : E → E →L[ℝ] ℝ} {f' : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) x :=
  hc.smul hf

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

def base (a : ι → ℝ) (B : Hermitian ι) : Mat ι := realDiagonal a + (B : Mat ι)

omit [Fintype ι] [Nonempty ι] in
theorem base_isHermitian (a : ι → ℝ) (B : Hermitian ι) :
    (base ι a B).IsHermitian :=
  (GibbsTraceDifferentiation.realDiagonal_isHermitian ι a).add
    (PreparedTraceForm.hermitian_isHermitian ι B)

def partitionHessianAt (a : ι → ℝ) (B : Hermitian ι) :
    Hermitian ι →L[ℝ] Hermitian ι →L[ℝ] ℝ :=
  (tracePair ι).comp ((expDerivative (base ι a B)).comp (GibbsFiniteResponse.inclusion ι))

omit [Nonempty ι] in
theorem partition_gradient_hasFDerivAt (a : ι → ℝ) (B : Hermitian ι) :
    HasFDerivAt (fderiv ℝ (partition ι a)) (partitionHessianAt ι a B) B := by
  have hinput : HasFDerivAt
      (fun K : Hermitian ι => realDiagonal a + (K : Mat ι))
      (GibbsFiniteResponse.inclusion ι) B :=
    (GibbsFiniteResponse.inclusion ι).hasFDerivAt.const_add (realDiagonal a)
  have hexp := (GibbsExponentialDifferentiation.exp_hasFDerivAt (base ι a B)).comp B hinput
  have hg : fderiv ℝ (partition ι a) =
      fun K : Hermitian ι => tracePair ι (NormedSpace.exp (realDiagonal a + (K : Mat ι))) := by
    funext K
    exact GibbsTraceDifferentiation.partition_fderiv ι a K
  rw [hg]
  simpa only [partitionHessianAt, ContinuousLinearMap.comp_assoc] using!
    hasFDerivAt_clm_comp_dual (E := Hermitian ι) (F := Mat ι)
      (L := by exact tracePair ι)
      (f := by exact fun K : Hermitian ι => NormedSpace.exp (realDiagonal a + (K : Mat ι)))
      (f' := by exact (expDerivative (base ι a B)).comp (GibbsFiniteResponse.inclusion ι))
      (x := B) (by exact hexp)

omit [Nonempty ι] in
theorem partitionHessianAt_apply (a : ι → ℝ) (B K J : Hermitian ι) :
    partitionHessianAt ι a B K J =
      realTrace ι (expDerivative (base ι a B) (K : Mat ι) * (J : Mat ι)) := rfl

def hessianAt (a : ι → ℝ) (B : Hermitian ι) :
    Hermitian ι →L[ℝ] Hermitian ι →L[ℝ] ℝ :=
  (partition ι a B)⁻¹ • partitionHessianAt ι a B +
    (-(partition ι a B ^ 2)⁻¹ • fderiv ℝ (partition ι a) B).smulRight
      (fderiv ℝ (partition ι a) B)

/-- The full derivative of the gradient, at a finite matrix observation. -/
theorem response_gradient_hasFDerivAt (a : ι → ℝ) (B : Hermitian ι) :
    HasFDerivAt (fderiv ℝ (response ι a)) (hessianAt ι a B) B := by
  have hpart : HasFDerivAt (partition ι a) (fderiv ℝ (partition ι a) B) B :=
    (GibbsTraceDifferentiation.partition_hasFDerivAt ι a B).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun K : Hermitian ι => (partition ι a K)⁻¹)
      (-(partition ι a B ^ 2)⁻¹ • fderiv ℝ (partition ι a) B) B := by
    simpa only [Function.comp_def] using!
      (hasDerivAt_inv (ne_of_gt (GibbsTraceDifferentiation.partition_pos ι a B))).comp_hasFDerivAt B hpart
  have h : HasFDerivAt
      (fun K : Hermitian ι => (partition ι a K)⁻¹ • fderiv ℝ (partition ι a) K)
      (hessianAt ι a B) B := by
    simpa only [hessianAt] using!
      hasFDerivAt_smul_dual hi (partition_gradient_hasFDerivAt ι a B)
  have hg : fderiv ℝ (response ι a) =
      fun K => (partition ι a K)⁻¹ • fderiv ℝ (partition ι a) K := by
    funext K
    exact GibbsConnectedResponse.response_fderiv ι a K
  rw [hg]
  exact h

theorem full_hessian (a : ι → ℝ) (B K J : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) B K J =
      realTrace ι (expDerivative (base ι a B) (K : Mat ι) * (J : Mat ι)) /
        partition ι a B -
      (realTrace ι (NormedSpace.exp (base ι a B) * (K : Mat ι)) / partition ι a B) *
        (realTrace ι (NormedSpace.exp (base ι a B) * (J : Mat ι)) / partition ι a B) := by
  rw [(response_gradient_hasFDerivAt ι a B).fderiv]
  simp only [hessianAt, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, partitionHessianAt_apply,
    GibbsTraceDifferentiation.partition_fderiv, GibbsTraceDifferentiation.tracePair_apply,
    base, div_eq_mul_inv]
  ring

/-- A coordinate change for observations, not a new choice of source. -/
def pullback (U : Matrix.unitaryGroup ι ℂ) (K : Hermitian ι) : Hermitian ι :=
  ⟨(Unitary.conjStarAlgAut ℝ (Mat ι) U).symm (K : Mat ι), by
    change star ((Unitary.conjStarAlgAut ℝ (Mat ι) U).symm (K : Mat ι)) = _
    rw [← map_star, K.property]⟩

omit [Nonempty ι] in
theorem conjugation_pullback (U : Matrix.unitaryGroup ι ℂ) (K : Hermitian ι) :
    conjugation ι U (pullback ι U K : Mat ι) = (K : Mat ι) :=
  (Unitary.conjStarAlgAut ℝ (Mat ι) U).apply_symm_apply _

omit [Nonempty ι] in
theorem pullback_scalar_iff (U : Matrix.unitaryGroup ι ℂ) (K : Hermitian ι) (r : ℝ) :
    (pullback ι U K : Mat ι) = r • (1 : Mat ι) ↔ (K : Mat ι) = r • (1 : Mat ι) := by
  constructor
  · intro h
    have hc := congrArg (conjugation ι U) h
    rw [conjugation_pullback, map_smul] at hc
    have h1 : conjugation ι U (1 : Mat ι) = 1 :=
      (Unitary.conjStarAlgAut ℝ (Mat ι) U).map_one
    rwa [h1] at hc
  · intro h
    change (Unitary.conjStarAlgAut ℝ (Mat ι) U).symm (K : Mat ι) = _
    rw [h, map_smul, map_one]

def spectralValues (a : ι → ℝ) (B : Hermitian ι) : ι → ℝ :=
  (base_isHermitian ι a B).eigenvalues

def spectralUnitary (a : ι → ℝ) (B : Hermitian ι) : Matrix.unitaryGroup ι ℂ :=
  (base_isHermitian ι a B).eigenvectorUnitary

omit [Nonempty ι] in
theorem base_spectral (a : ι → ℝ) (B : Hermitian ι) :
    base ι a B = conjugation ι (spectralUnitary ι a B) (realDiagonal (spectralValues ι a B)) :=
  (base_isHermitian ι a B).spectral_theorem

omit [Nonempty ι] in
theorem partition_spectral (a : ι → ℝ) (B : Hermitian ι) :
    partition ι a B = GibbsTraceForm.Z (spectralValues ι a B) := by
  change realTrace ι (NormedSpace.exp (base ι a B)) = _
  rw [base_spectral, ← GibbsTraceDifferentiation.conjugation_exp,
    GibbsTraceDifferentiation.realTrace_conjugation]
  have hp := GibbsConnectedResponse.partition_zero ι (spectralValues ι a B)
  change realTrace ι (NormedSpace.exp (realDiagonal (spectralValues ι a B) + 0)) = _ at hp
  simpa only [add_zero] using hp

/-- The same unitary acts on both directions. Thus no off-diagonal or
mixed response is discarded in reducing to the positive trace form. -/
theorem hessian_spectral (a : ι → ℝ) (B K J : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) B K J =
      GibbsTraceForm.gibbsForm (spectralValues ι a B)
        (pullback ι (spectralUnitary ι a B) K : Mat ι)
        (pullback ι (spectralUnitary ι a B) J : Mat ι) := by
  let U := spectralUnitary ι a B
  let v := spectralValues ι a B
  let K' := (pullback ι U K : Mat ι)
  let J' := (pullback ι U J : Mat ι)
  have hK : conjugation ι U K' = (K : Mat ι) := conjugation_pullback ι U K
  have hJ : conjugation ι U J' = (J : Mat ι) := conjugation_pullback ι U J
  have hp : realTrace ι (expDerivative (base ι a B) (K : Mat ι) * (J : Mat ι)) =
      GibbsTraceForm.responsePairing v K' J' := by
    rw [← hK, ← hJ, base_spectral, GibbsTraceDifferentiation.expDerivative_conjugation,
      ← GibbsTraceDifferentiation.conjugation_mul,
      GibbsTraceDifferentiation.realTrace_conjugation,
      GibbsExponentialDifferentiation.expDerivative_realDiagonal]
    rfl
  have hm (H : Hermitian ι) :
      realTrace ι (NormedSpace.exp (base ι a B) * (H : Mat ι)) =
        GibbsTraceForm.weightedTrace v (pullback ι U H : Mat ι) := by
    have hH := conjugation_pullback ι U H
    rw [← hH, base_spectral, ← GibbsTraceDifferentiation.conjugation_exp,
      ← GibbsTraceDifferentiation.conjugation_mul,
      GibbsTraceDifferentiation.realTrace_conjugation,
      GibbsExponentialDifferentiation.exp_realDiagonal]
    rfl
  rw [full_hessian, hp, hm K, hm J, partition_spectral]
  simp only [GibbsTraceForm.gibbsForm_apply, GibbsTraceForm.mean_apply]
  rfl

theorem hessian_squares (a : ι → ℝ) (B K : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) B K K =
      GibbsTraceForm.weightedNormSq (spectralValues ι a B)
        (GibbsTraceForm.centered (spectralValues ι a B)
          (pullback ι (spectralUnitary ι a B) K : Mat ι)) /
            GibbsTraceForm.Z (spectralValues ι a B) := by
  rw [hessian_spectral]
  exact GibbsTraceForm.gibbsForm_self_normSq _
    (PreparedTraceForm.hermitian_isHermitian _ _)

theorem hessian_nonneg (a : ι → ℝ) (B K : Hermitian ι) :
    0 ≤ fderiv ℝ (fderiv ℝ (response ι a)) B K K := by
  rw [hessian_spectral]
  exact GibbsTraceForm.gibbsForm_nonneg _ (PreparedTraceForm.hermitian_isHermitian _ _)

theorem hessian_self_zero_iff (a : ι → ℝ) (B K : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) B K K = 0 ↔
      ∃ r : ℝ, (K : Mat ι) = r • (1 : Mat ι) := by
  rw [hessian_spectral,
    GibbsTraceForm.gibbsForm_self_eq_zero_iff _ (PreparedTraceForm.hermitian_isHermitian _ _)]
  exact exists_congr fun r => pullback_scalar_iff ι _ K r

theorem hessian_kernel (a : ι → ℝ) (B K : Hermitian ι) :
    (∀ J : Hermitian ι, fderiv ℝ (fderiv ℝ (response ι a)) B K J = 0) ↔
      ∃ r : ℝ, (K : Mat ι) = r • (1 : Mat ι) := by
  constructor
  · intro h
    exact (hessian_self_zero_iff ι a B K).mp (h K)
  · rintro ⟨r, hr⟩ J
    rw [hessian_spectral, (pullback_scalar_iff ι _ K r).mpr hr]
    exact GibbsTraceForm.gibbsForm_scalar_left _ r _

theorem hessian_traceless_pos (a : ι → ℝ) (B : Hermitian ι)
    (K : Traceless ι) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response ι a)) B K.val K.val := by
  refine lt_of_le_of_ne (hessian_nonneg ι a B K.val) ?_
  intro hz
  obtain ⟨r, hr⟩ := (hessian_self_zero_iff ι a B K.val).mp hz.symm
  have hz0 : GibbsTraceForm.gibbsForm a (K.val : Mat ι) (K.val : Mat ι) = 0 := by
    rw [hr]
    exact GibbsTraceForm.gibbsForm_scalar_left _ _ _
  exact (ne_of_gt (GibbsTraceForm.gibbsForm_traceless_pos a K hK)) hz0

end GeneratedFoundations.Operations.GibbsFullResponse
