module

public import GeneratedFoundations.Source.PlaneGenerator

/-!
# Complex Hilbert structure of the minimal real carrier

A normalized quarter-turn extends real scalar multiplication to complex
scalar multiplication on the same carrier. The original norm is retained.
The resulting complex Hilbert space has dimension one. The manuscript uses
the first-slot-linear Hermitian form; the library inner product is its
complex conjugate.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Source.ComplexStructure

open PlaneGenerator
open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def scalarAction (e : V ≃ₗᵢ[ℝ] ℂ) : ℂ →ₐ[ℝ] Module.End ℝ V :=
  complexScalarAction (generator e) (generator_square e)

theorem scalarAction_coordinate (e : V ≃ₗᵢ[ℝ] ℂ) (z : ℂ) (v : V) :
    e (scalarAction e z v) = z * e v := by
  rw [scalarAction, complexScalarAction_apply, map_add, e.map_smul, e.map_smul,
    generator_coordinate]
  apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

@[instance_reducible] def complexModule (e : V ≃ₗᵢ[ℝ] ℂ) : Module ℂ V :=
  Module.compHom V (scalarAction e).toRingHom

@[instance_reducible] def complexNormedSpace (e : V ≃ₗᵢ[ℝ] ℂ) : NormedSpace ℂ V :=
  { complexModule e with
    norm_smul_le := by
      intro z v
      change ‖scalarAction e z v‖ ≤ ‖z‖ * ‖v‖
      rw [← e.norm_map (scalarAction e z v), scalarAction_coordinate, norm_mul, e.norm_map] }

@[instance_reducible] def complexInnerProductSpace (e : V ≃ₗᵢ[ℝ] ℂ) : InnerProductSpace ℂ V :=
  { complexNormedSpace e with
    inner := fun v w => inner ℂ (e v) (e w)
    norm_sq_eq_re_inner := by
      intro v
      rw [← e.norm_map v]
      exact norm_sq_eq_re_inner (e v)
    conj_inner_symm := by
      intro v w
      exact inner_conj_symm _ _
    add_left := by
      intro v w u
      rw [map_add, inner_add_left]
    smul_left := by
      intro v w z
      change inner ℂ (e (scalarAction e z v)) (e w) = _
      rw [scalarAction_coordinate]
      exact inner_smul_left _ _ _ }

theorem complex_smul_eq (e : V ≃ₗᵢ[ℝ] ℂ) (z : ℂ) (v : V) :
    letI := complexInnerProductSpace e
    z • v = z.re • v + z.im • generator e v :=
  complexScalarAction_apply (generator e) (generator_square e) z v

def coordinate (e : V ≃ₗᵢ[ℝ] ℂ) :
    letI := complexInnerProductSpace e
    V ≃ₗᵢ[ℂ] ℂ := by
  letI := complexInnerProductSpace e
  exact
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun z v => scalarAction_coordinate e z v
      norm_map' := e.norm_map }

theorem complex_finrank_one (e : V ≃ₗᵢ[ℝ] ℂ) :
    letI := complexInnerProductSpace e
    Module.finrank ℂ V = 1 := by
  let _ := complexInnerProductSpace e
  exact (coordinate e).toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

theorem completeSpace (e : V ≃ₗᵢ[ℝ] ℂ) : CompleteSpace V :=
  e.toIsometryEquiv.completeSpace

def sourceHermitian (J : Module.End ℝ V) (v w : V) : ℂ :=
  (inner ℝ v w : ℂ) - Complex.I * (inner ℝ (J v) w : ℂ)

theorem sourceHermitian_coordinate (e : V ≃ₗᵢ[ℝ] ℂ) (v w : V) :
    sourceHermitian (generator e) v w = e v * conj (e w) := by
  unfold sourceHermitian
  rw [inner_map_complex e, inner_map_complex e, generator_coordinate]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem sourceHermitian_conj_symm (e : V ≃ₗᵢ[ℝ] ℂ) (v w : V) :
    conj (sourceHermitian (generator e) w v) = sourceHermitian (generator e) v w := by
  simp only [sourceHermitian_coordinate, map_mul, starRingEnd_self_apply]
  ring

theorem sourceHermitian_add_left (J : Module.End ℝ V) (v w u : V) :
    sourceHermitian J (v + w) u = sourceHermitian J v u + sourceHermitian J w u := by
  simp only [sourceHermitian, map_add, inner_add_left, Complex.ofReal_add]
  ring

theorem sourceHermitian_scalar_left (e : V ≃ₗᵢ[ℝ] ℂ) (z : ℂ) (v w : V) :
    sourceHermitian (generator e) (scalarAction e z v) w =
      z * sourceHermitian (generator e) v w := by
  simp only [sourceHermitian_coordinate, scalarAction_coordinate]
  ring

theorem sourceHermitian_self (e : V ≃ₗᵢ[ℝ] ℂ) (v : V) :
    sourceHermitian (generator e) v v = (‖v‖ ^ 2 : ℝ) := by
  rw [sourceHermitian_coordinate, Complex.mul_conj, ← Complex.sq_norm, e.norm_map]

theorem sourceHermitian_positive (e : V ≃ₗᵢ[ℝ] ℂ) (v : V) (hv : v ≠ 0) :
    0 < (sourceHermitian (generator e) v v).re := by
  rw [sourceHermitian_self, Complex.ofReal_re]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

theorem inner_convention (e : V ≃ₗᵢ[ℝ] ℂ) (v w : V) :
    letI := complexInnerProductSpace e
    inner ℂ v w = conj (sourceHermitian (generator e) v w) := by
  change inner ℂ (e v) (e w) = _
  simp only [sourceHermitian_coordinate, map_mul, starRingEnd_self_apply, RCLike.inner_apply]
  ring

theorem sourceHermitian_neg (J : Module.End ℝ V) (v w : V) :
    sourceHermitian (-J) v w = conj (sourceHermitian J v w) := by
  simp [sourceHermitian]

theorem sourceHermitian_unique (e : V ≃ₗᵢ[ℝ] ℂ) (F : V → V → ℂ)
    (hreal : ∀ v w, (F v w).re = inner ℝ v w)
    (hI : ∀ v w, F (generator e v) w = Complex.I * F v w) :
    F = sourceHermitian (generator e) := by
  funext v w
  apply Complex.ext
  · simp [sourceHermitian, hreal]
  · have h := hreal (generator e v) w
    rw [hI] at h
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub] at h
    simpa [sourceHermitian] using (neg_eq_iff_eq_neg.mp h)

def reverseCoordinate (e : V ≃ₗᵢ[ℝ] ℂ) : V ≃ₗᵢ[ℝ] ℂ :=
  e.trans Complex.conjLIE

theorem reverseCoordinate_generator (e : V ≃ₗᵢ[ℝ] ℂ) :
    generator (reverseCoordinate e) = -generator e := by
  ext v
  apply e.injective
  have h := congrArg (starRingEnd ℂ) (generator_coordinate (reverseCoordinate e) v)
  simpa [reverseCoordinate] using h

theorem reverseCoordinate_sourceHermitian (e : V ≃ₗᵢ[ℝ] ℂ) (v w : V) :
    sourceHermitian (generator (reverseCoordinate e)) v w =
      conj (sourceHermitian (generator e) v w) := by
  rw [reverseCoordinate_generator, sourceHermitian_neg]

theorem minimalCarrier_complexHilbert
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (f : d.Changes ≃* Circle),
      Continuous f ∧ Continuous f.symm ∧
        (letI := complexInnerProductSpace e
         Module.finrank ℂ d.Carrier = 1 ∧
           ∀ g v, d.action g v = (f g : ℂ) • v) := by
  obtain ⟨_, e, f, hfc, hfi, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  refine ⟨e, f, hfc, hfi, complex_finrank_one e, ?_⟩
  intro g v
  apply e.injective
  exact (haction g v).trans (scalarAction_coordinate e (f g : ℂ) v).symm

end GeneratedFoundations.Source.ComplexStructure
