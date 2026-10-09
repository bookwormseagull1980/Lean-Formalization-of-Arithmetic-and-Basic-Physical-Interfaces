module

public import GeneratedFoundations.Spectral.PhysicalWindowOperator
public import GeneratedFoundations.Spectral.NeumannSpectrum
public import GeneratedFoundations.Spectral.NeumannSpectralProjections

/-!
# The Neumann spectrum on the generated interval

Translation transports the complete cosine basis, the original Sobolev
domain and bounded two-sided resolvents. The spectrum on the correlation
window is consequently the full spectrum of its differential operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace
open scoped LinearPMap

namespace GeneratedFoundations.Spectral

/-- The spectral shift of the differential operator on its Sobolev domain. -/
def intervalNeumannShift {a b : ℝ} (hab : a < b) (z : ℂ) :
    complexNeumannDomain a b →ₗ[ℂ] ComplexIntervalL2 a b := by
  let T : complexNeumannDomain a b →ₗ[ℂ] ComplexIntervalL2 a b :=
    (complexNeumannOperator hab).toFun
  exact T - z • (complexNeumannDomain a b).subtype

theorem intervalNeumannShift_apply {a b : ℝ} (hab : a < b) (z : ℂ)
    (u : complexNeumannDomain a b) :
    intervalNeumannShift hab z u = (complexNeumannOperator hab).toFun u -
      z • (u : ComplexIntervalL2 a b) := rfl

/-- A bounded two-sided inverse with range in the actual Neumann domain. -/
structure IsIntervalNeumannResolvent {a b : ℝ} (hab : a < b) (z : ℂ)
    (S : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b) : Prop where
  mem_domain : ∀ f, S f ∈ complexNeumannDomain a b
  right_inverse : ∀ f, intervalNeumannShift hab z ⟨S f, mem_domain f⟩ = f
  left_inverse : ∀ u : complexNeumannDomain a b,
    S (intervalNeumannShift hab z u) = (u : ComplexIntervalL2 a b)

def intervalNeumannResolventSet {a b : ℝ} (hab : a < b) : Set ℂ :=
  {z | ∃ S : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b,
    IsIntervalNeumannResolvent hab z S}

def intervalNeumannSpectrum {a b : ℝ} (hab : a < b) : Set ℂ :=
  (intervalNeumannResolventSet hab)ᶜ

theorem IsIntervalNeumannResolvent.unique {a b : ℝ} {hab : a < b} {z : ℂ}
    {S T : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b}
    (hS : IsIntervalNeumannResolvent hab z S)
    (hT : IsIntervalNeumannResolvent hab z T) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    S f = S (intervalNeumannShift hab z ⟨T f, hT.mem_domain f⟩) := by
      rw [hT.right_inverse]
    _ = T f := hS.left_inverse ⟨T f, hT.mem_domain f⟩

section Translation

variable (a L : ℝ) [hL : Fact (0 < L)]

theorem translateNeumannDomainEquiv_symm_toL2
    (u : complexNeumannDomain 0 L) :
    ((translateNeumannDomainEquiv (a := a) hL.out).symm u :
      ComplexIntervalL2 a (a + L)) =
        (shiftCanonicalL2Equiv (a := a) (L := L)).symm u := by
  apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (translateNeumannDomainEquiv_toL2 hL.out
    ((translateNeumannDomainEquiv (a := a) hL.out).symm u)).symm.trans
      (congrArg Subtype.val
        ((translateNeumannDomainEquiv (a := a) hL.out).apply_symm_apply u))

theorem mem_translatedNeumannDomain_iff (f : ComplexIntervalL2 a (a + L)) :
    f ∈ complexNeumannDomain a (a + L) ↔
      shiftCanonicalL2Equiv f ∈ complexNeumannDomain 0 L := by
  constructor
  · intro hf
    rw [← translateNeumannDomainEquiv_toL2 hL.out ⟨f, hf⟩]
    exact (translateNeumannDomainEquiv hL.out ⟨f, hf⟩).property
  · intro hf
    have h := ((translateNeumannDomainEquiv (a := a) hL.out).symm
      ⟨shiftCanonicalL2Equiv f, hf⟩).property
    rw [translateNeumannDomainEquiv_symm_toL2,
      LinearIsometryEquiv.symm_apply_apply] at h
    exact h

theorem translate_intervalNeumannShift (z : ℂ)
    (u : complexNeumannDomain a (a + L)) :
    shiftCanonicalL2Equiv
        (intervalNeumannShift (by linarith [hL.out] : a < a + L) z u) =
      neumannShift L z (translateNeumannDomainEquiv hL.out u) := by
  calc
    _ = (complexNeumannOperator hL.out).toFun (translateNeumannDomainEquiv hL.out u) -
        z • (translateNeumannDomainEquiv hL.out u : ComplexIntervalL2 0 L) := by
      rw [intervalNeumannShift_apply, map_sub, map_smul,
        complexNeumannOperator_translate hL.out, translateNeumannDomainEquiv_toL2]
    _ = _ := rfl

def translatedNeumannResolvent
    (S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L) :
    ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L) :=
  ((shiftCanonicalL2Equiv (a := a) (L := L)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (S.comp (shiftCanonicalL2Equiv (a := a) (L := L)).toContinuousLinearEquiv.toContinuousLinearMap)

omit hL in
theorem translatedNeumannResolvent_apply
    (S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L)
    (f : ComplexIntervalL2 a (a + L)) :
    translatedNeumannResolvent a L S f =
      (shiftCanonicalL2Equiv (a := a) (L := L)).symm
        (S (shiftCanonicalL2Equiv f)) := rfl

omit hL in
theorem translatedNeumannResolvent_isCompact
    {S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsCompactOperator S) : IsCompactOperator (translatedNeumannResolvent a L S) :=
  (hS.comp_clm
    (shiftCanonicalL2Equiv (a := a) (L := L)).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      (shiftCanonicalL2Equiv (a := a) (L := L)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem translatedNeumannResolvent_mem_domain {z : ℂ}
    {S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsNeumannResolvent L z S) (f : ComplexIntervalL2 a (a + L)) :
    translatedNeumannResolvent a L S f ∈ complexNeumannDomain a (a + L) := by
  apply (mem_translatedNeumannDomain_iff a L _).mpr
  rw [translatedNeumannResolvent_apply, LinearIsometryEquiv.apply_symm_apply]
  exact hS.mem_domain _

theorem translatedNeumannResolvent_spec {z : ℂ}
    {S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsNeumannResolvent L z S) :
    IsIntervalNeumannResolvent (by linarith [hL.out] : a < a + L) z
      (translatedNeumannResolvent a L S) where
  mem_domain := translatedNeumannResolvent_mem_domain a L hS
  right_inverse := by
    intro f
    let u : complexNeumannDomain a (a + L) :=
      ⟨translatedNeumannResolvent a L S f,
        translatedNeumannResolvent_mem_domain a L hS f⟩
    have hu : translateNeumannDomainEquiv hL.out u =
        ⟨S (shiftCanonicalL2Equiv f), hS.mem_domain _⟩ := by
      apply Subtype.ext
      rw [translateNeumannDomainEquiv_toL2]
      change shiftCanonicalL2Equiv
        ((shiftCanonicalL2Equiv (a := a) (L := L)).symm
          (S (shiftCanonicalL2Equiv f))) = _
      exact LinearIsometryEquiv.apply_symm_apply _ _
    apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
    change shiftCanonicalL2Equiv
      (intervalNeumannShift (by linarith [hL.out] : a < a + L) z u) = _
    rw [translate_intervalNeumannShift, hu]
    exact hS.right_inverse (shiftCanonicalL2Equiv f)
  left_inverse := by
    intro u
    apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
    rw [translatedNeumannResolvent_apply, LinearIsometryEquiv.apply_symm_apply,
      translate_intervalNeumannShift]
    exact (hS.left_inverse (translateNeumannDomainEquiv hL.out u)).trans
      (translateNeumannDomainEquiv_toL2 hL.out u)

theorem IsIntervalNeumannResolvent.not_eigenvalue {z : ℂ}
    {S : ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L)}
    (hS : IsIntervalNeumannResolvent (by linarith [hL.out] : a < a + L) z S)
    (n : ℕ) : z ≠ (neumannEigenvalue L n : ℂ) := by
  intro hz
  subst z
  let v : complexNeumannDomain 0 L :=
    ⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩
  let u := (translateNeumannDomainEquiv (a := a) hL.out).symm v
  have hTu : translateNeumannDomainEquiv hL.out u = v :=
    (translateNeumannDomainEquiv (a := a) hL.out).apply_symm_apply v
  have hUv : shiftCanonicalL2Equiv (u : ComplexIntervalL2 a (a + L)) =
      neumannCosineMode L n :=
    (translateNeumannDomainEquiv_toL2 hL.out u).symm.trans
      (congrArg Subtype.val hTu)
  have hne : (u : ComplexIntervalL2 a (a + L)) ≠ 0 := by
    intro hu
    rw [hu, map_zero] at hUv
    exact (neumannCosineMode_orthonormal L).ne_zero n hUv.symm
  have hzero : intervalNeumannShift (by linarith [hL.out] : a < a + L)
      (neumannEigenvalue L n : ℂ) u = 0 := by
    apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
    rw [translate_intervalNeumannShift, hTu, map_zero]
    change neumannShift L (neumannEigenvalue L n : ℂ)
      ⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩ = 0
    rw [neumannShift_apply, complexNeumannOperator_cosine, sub_self]
  have h := hS.left_inverse u
  rw [hzero, map_zero] at h
  exact hne h.symm

theorem mem_intervalNeumannResolventSet_iff (z : ℂ) :
    z ∈ intervalNeumannResolventSet (by linarith [hL.out] : a < a + L) ↔
      ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ n
    exact IsIntervalNeumannResolvent.not_eigenvalue a L hS n
  · intro hz
    exact ⟨translatedNeumannResolvent a L (neumannShiftResolvent L z hz),
      translatedNeumannResolvent_spec a L (neumannShiftResolvent_spec L z hz)⟩

/-- Equality of the full resolvent sets, with two-sided inverses on both domains. -/
theorem intervalNeumannResolventSet_eq :
    intervalNeumannResolventSet (by linarith [hL.out] : a < a + L) = neumannResolventSet L := by
  ext z
  rw [mem_intervalNeumannResolventSet_iff, mem_neumannResolventSet_iff]

theorem intervalNeumannSpectrum_eq_range :
    intervalNeumannSpectrum (by linarith [hL.out] : a < a + L) =
      Set.range (fun n : ℕ => (neumannEigenvalue L n : ℂ)) := by
  unfold intervalNeumannSpectrum
  rw [intervalNeumannResolventSet_eq]
  exact neumannSpectrum_eq_range L

theorem translatedIntervalNeumannResolvent_existsUnique (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    ∃! S : ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L),
      IsIntervalNeumannResolvent (by linarith [hL.out] : a < a + L) z S := by
  refine ⟨translatedNeumannResolvent a L (neumannShiftResolvent L z hz),
    translatedNeumannResolvent_spec a L (neumannShiftResolvent_spec L z hz), ?_⟩
  intro S hS
  exact IsIntervalNeumannResolvent.unique hS
    (translatedNeumannResolvent_spec a L (neumannShiftResolvent_spec L z hz))

theorem translatedIntervalNeumannResolvent_isCompact {z : ℂ}
    {S : ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L)}
    (hS : IsIntervalNeumannResolvent (by linarith [hL.out] : a < a + L) z S) :
    IsCompactOperator S := by
  have hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ) :=
    IsIntervalNeumannResolvent.not_eigenvalue a L hS
  rw [IsIntervalNeumannResolvent.unique hS
    (translatedNeumannResolvent_spec a L (neumannShiftResolvent_spec L z hz))]
  exact translatedNeumannResolvent_isCompact a L (neumannShiftResolvent_isCompact L z hz)

def translatedNeumannCosineMode (n : ℕ) : ComplexIntervalL2 a (a + L) :=
  (shiftCanonicalL2Equiv (a := a) (L := L)).symm (neumannCosineMode L n)

def translatedNeumannCosineBasis : HilbertBasis ℕ ℂ (ComplexIntervalL2 a (a + L)) :=
  HilbertBasis.ofRepr ((shiftCanonicalL2Equiv (a := a) (L := L)).trans
    (neumannCosineBasis L).repr)

theorem coe_translatedNeumannCosineBasis :
    ⇑(translatedNeumannCosineBasis a L) = translatedNeumannCosineMode a L := by
  funext n
  change (shiftCanonicalL2Equiv (a := a) (L := L)).symm ((neumannCosineBasis L) n) = _
  rw [coe_neumannCosineBasis]
  rfl

theorem translatedNeumannCosineMode_inner (n : ℕ)
    (f : ComplexIntervalL2 a (a + L)) :
    inner ℂ (translatedNeumannCosineMode a L n) f =
      inner ℂ (neumannCosineMode L n) (shiftCanonicalL2Equiv f) := by
  calc
    _ = inner ℂ (shiftCanonicalL2Equiv (translatedNeumannCosineMode a L n))
        (shiftCanonicalL2Equiv f) :=
      ((shiftCanonicalL2Equiv (a := a) (L := L)).inner_map_map _ _).symm
    _ = _ := by rw [translatedNeumannCosineMode, LinearIsometryEquiv.apply_symm_apply]

theorem translatedNeumannCosineBasis_hasSum (f : ComplexIntervalL2 a (a + L)) :
    HasSum (fun n => inner ℂ (translatedNeumannCosineMode a L n) f •
      translatedNeumannCosineMode a L n) f := by
  simpa only [HilbertBasis.repr_apply_apply, coe_translatedNeumannCosineBasis] using
    (translatedNeumannCosineBasis a L).hasSum_repr f

theorem translatedNeumannCosineMode_orthonormal :
    Orthonormal ℂ (translatedNeumannCosineMode a L) := by
  simpa only [coe_translatedNeumannCosineBasis] using
    (translatedNeumannCosineBasis a L).orthonormal

theorem translatedNeumannCosineMode_mem_domain (n : ℕ) :
    translatedNeumannCosineMode a L n ∈ complexNeumannDomain a (a + L) := by
  apply (mem_translatedNeumannDomain_iff a L _).mpr
  rw [translatedNeumannCosineMode, LinearIsometryEquiv.apply_symm_apply]
  exact neumannCosineMode_mem_domain L n

theorem translatedNeumann_domain_iff (f : ComplexIntervalL2 a (a + L)) :
    f ∈ complexNeumannDomain a (a + L) ↔
      Summable (fun n : ℕ => (neumannEigenvalue L n) ^ 2 *
        ‖inner ℂ (translatedNeumannCosineMode a L n) f‖ ^ 2) := by
  rw [mem_translatedNeumannDomain_iff]
  simp_rw [translatedNeumannCosineMode_inner]
  exact complexNeumann_domain_iff L _

theorem translatedNeumannOperator_coefficients
    (f : complexNeumannDomain a (a + L)) (n : ℕ) :
    inner ℂ (translatedNeumannCosineMode a L n)
        ((complexNeumannOperator (by linarith [hL.out] : a < a + L)).toFun f) =
      (neumannEigenvalue L n : ℂ) *
        inner ℂ (translatedNeumannCosineMode a L n) (f : ComplexIntervalL2 a (a + L)) := by
  rw [translatedNeumannCosineMode_inner, complexNeumannOperator_translate hL.out]
  have h := complexNeumannOperator_coefficients L
    (translateNeumannDomainEquiv hL.out f) n
  rw [translateNeumannDomainEquiv_toL2] at h
  exact h.trans (congrArg (fun c : ℂ => (neumannEigenvalue L n : ℂ) * c)
    (translatedNeumannCosineMode_inner a L n f).symm)

/-- Every eigenspace of the translated differential operator is one cosine line. -/
theorem translatedNeumann_eigenvector_iff (n : ℕ)
    (f : complexNeumannDomain a (a + L)) :
    (complexNeumannOperator (by linarith [hL.out] : a < a + L)).toFun f =
        (neumannEigenvalue L n : ℂ) • (f : ComplexIntervalL2 a (a + L)) ↔
      ∃ c : ℂ, (f : ComplexIntervalL2 a (a + L)) =
        c • translatedNeumannCosineMode a L n := by
  constructor
  · intro hf
    have he : (complexNeumannOperator hL.out).toFun
        (translateNeumannDomainEquiv hL.out f) =
          (neumannEigenvalue L n : ℂ) •
            (translateNeumannDomainEquiv hL.out f : ComplexIntervalL2 0 L) := by
      rw [translateNeumannDomainEquiv_toL2, ← complexNeumannOperator_translate hL.out,
        hf, map_smul]
    obtain ⟨c, hc⟩ := (complexNeumann_eigenvector_iff L n
      (translateNeumannDomainEquiv hL.out f)).mp he
    refine ⟨c, (shiftCanonicalL2Equiv (a := a) (L := L)).injective ?_⟩
    rw [map_smul, translatedNeumannCosineMode, LinearIsometryEquiv.apply_symm_apply]
    exact (translateNeumannDomainEquiv_toL2 hL.out f).symm.trans hc
  · rintro ⟨c, hc⟩
    apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
    rw [complexNeumannOperator_translate hL.out, map_smul,
      ← translateNeumannDomainEquiv_toL2 hL.out f]
    apply (complexNeumann_eigenvector_iff L n
      (translateNeumannDomainEquiv hL.out f)).mpr
    refine ⟨c, ?_⟩
    rw [translateNeumannDomainEquiv_toL2, hc, map_smul,
      translatedNeumannCosineMode, LinearIsometryEquiv.apply_symm_apply]

def translatedNeumannCosineProjection (n : ℕ) :
    ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L) :=
  rankOne ℂ (translatedNeumannCosineMode a L n) (translatedNeumannCosineMode a L n)

theorem translatedNeumannCosineProjection_apply (n : ℕ)
    (f : ComplexIntervalL2 a (a + L)) :
    translatedNeumannCosineProjection a L n f =
      inner ℂ (translatedNeumannCosineMode a L n) f • translatedNeumannCosineMode a L n :=
  rankOne_apply _ _ _

theorem translatedNeumannCosineProjection_orthogonal (n : ℕ) :
    IsStarProjection (translatedNeumannCosineProjection a L n) :=
  isStarProjection_rankOne_self ((translatedNeumannCosineMode_orthonormal a L).norm_eq_one n)

theorem translatedNeumannCosineProjection_self (n : ℕ) :
    translatedNeumannCosineProjection a L n (translatedNeumannCosineMode a L n) =
      translatedNeumannCosineMode a L n := by
  rw [translatedNeumannCosineProjection_apply,
    orthonormal_iff_ite.mp (translatedNeumannCosineMode_orthonormal a L)]
  simp

theorem translatedNeumannCosineProjection_range (n : ℕ) :
    (translatedNeumannCosineProjection a L n).range =
      Submodule.span ℂ {translatedNeumannCosineMode a L n} := by
  ext f
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨inner ℂ (translatedNeumannCosineMode a L n) g,
      (translatedNeumannCosineProjection_apply a L n g).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • translatedNeumannCosineMode a L n, ?_⟩
    change translatedNeumannCosineProjection a L n
      (c • translatedNeumannCosineMode a L n) = _
    rw [map_smul, translatedNeumannCosineProjection_self]

/-- The projection range is an eigenspace of the original differential operator. -/
theorem translatedNeumannCosineProjection_range_iff (n : ℕ)
    (f : ComplexIntervalL2 a (a + L)) :
    f ∈ (translatedNeumannCosineProjection a L n).range ↔
      ∃ u : complexNeumannDomain a (a + L), (u : ComplexIntervalL2 a (a + L)) = f ∧
        (complexNeumannOperator (by linarith [hL.out] : a < a + L)).toFun u =
          (neumannEigenvalue L n : ℂ) • (u : ComplexIntervalL2 a (a + L)) := by
  rw [translatedNeumannCosineProjection_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    let u : complexNeumannDomain a (a + L) :=
      c • ⟨translatedNeumannCosineMode a L n, translatedNeumannCosineMode_mem_domain a L n⟩
    refine ⟨u, hc, (translatedNeumann_eigenvector_iff a L n u).mpr ⟨c, rfl⟩⟩
  · rintro ⟨u, hu, he⟩
    obtain ⟨c, hc⟩ := (translatedNeumann_eigenvector_iff a L n u).mp he
    exact ⟨c, hc.symm.trans hu⟩

theorem translatedNeumannCosineProjection_unique (n : ℕ)
    (P : ComplexIntervalL2 a (a + L) →L[ℂ] ComplexIntervalL2 a (a + L))
    (hP : IsStarProjection P)
    (hrange : P.range = Submodule.span ℂ {translatedNeumannCosineMode a L n}) :
    P = translatedNeumannCosineProjection a L n :=
  ContinuousLinearMap.IsStarProjection.ext hP (translatedNeumannCosineProjection_orthogonal a L n)
    (hrange.trans (translatedNeumannCosineProjection_range a L n).symm)

theorem translateNeumannCosineProjection (n : ℕ) (f : ComplexIntervalL2 a (a + L)) :
    shiftCanonicalL2Equiv (translatedNeumannCosineProjection a L n f) =
      NeumannSpectralProjections.cosineProjection L n (shiftCanonicalL2Equiv f) := by
  rw [translatedNeumannCosineProjection_apply, map_smul, translatedNeumannCosineMode_inner,
    translatedNeumannCosineMode, LinearIsometryEquiv.apply_symm_apply,
    NeumannSpectralProjections.cosineProjection_apply]

theorem translatedNeumannCosineProjection_resolution (f : ComplexIntervalL2 a (a + L)) :
    HasSum (fun n => translatedNeumannCosineProjection a L n f) f := by
  simpa only [translatedNeumannCosineProjection_apply] using
    translatedNeumannCosineBasis_hasSum a L f

/-- The transported positive modes have the usual shifted cosine representatives. -/
theorem translatedNeumannCosineMode_succ_coe (n : ℕ) :
    translatedNeumannCosineMode a L (n + 1) =ᵐ[intervalMeasure a (a + L)]
      fun x => (Real.sqrt L : ℂ)⁻¹ * (Real.sqrt 2 : ℂ) *
        (Real.cos ((n + 1 : ℕ) * Real.pi * (x - a) / L) : ℂ) := by
  have hp := (shiftLeft_measurePreserving (a := a) (L := L)).quasiMeasurePreserving.ae
    (neumannCosineMode_succ_coe L n)
  have hc : translatedNeumannCosineMode a L (n + 1) =ᵐ[intervalMeasure a (a + L)]
      fun x => neumannCosineMode L (n + 1) (shiftLeft a x) :=
    Lp.coeFn_compMeasurePreserving (neumannCosineMode L (n + 1))
      (shiftLeft_measurePreserving (a := a) (L := L))
  simpa only [Function.comp_def, shiftLeft] using hc.trans hp

end Translation

/-- Compactness concerns every bounded inverse of the original differential operator. -/
theorem IsIntervalNeumannResolvent.isCompact {a b : ℝ} {hab : a < b} {z : ℂ}
    {S : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b}
    (hS : IsIntervalNeumannResolvent hab z S) : IsCompactOperator S := by
  let _ : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have heq : a + (b - a) = b := by ring
  have ha : a < a + (b - a) := by linarith
  have h : ∀ T : ComplexIntervalL2 a (a + (b - a)) →L[ℂ]
      ComplexIntervalL2 a (a + (b - a)),
       IsIntervalNeumannResolvent ha z T →
        IsCompactOperator T := fun _ hT =>
    translatedIntervalNeumannResolvent_isCompact a (b - a) hT
  have h' : ∀ T : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b,
      IsIntervalNeumannResolvent hab z T → IsCompactOperator T := by
    generalize a + (b - a) = c at ha h heq
    subst c
    exact h
  exact h' S hS

theorem intervalNeumannResolvent_existsUnique {a b : ℝ} (hab : a < b) (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue (b - a) n : ℂ)) :
    ∃! S : ComplexIntervalL2 a b →L[ℂ] ComplexIntervalL2 a b,
      IsIntervalNeumannResolvent hab z S := by
  let _ : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have heq : a + (b - a) = b := by ring
  have ha : a < a + (b - a) := by linarith
  have h : ∃! S : ComplexIntervalL2 a (a + (b - a)) →L[ℂ]
      ComplexIntervalL2 a (a + (b - a)), IsIntervalNeumannResolvent ha z S :=
    translatedIntervalNeumannResolvent_existsUnique a (b - a) z hz
  generalize a + (b - a) = c at ha h heq
  subst c
  exact h

/-- The actual correlation endpoints carry exactly the Neumann eigenvalue spectrum. -/
theorem generatedWindow_neumannSpectrum {b : ℝ} (hb : 0 < b) :
    intervalNeumannSpectrum (sub_pos.mp (windowLengthGenerated_pos hb)) =
      Set.range (fun n : ℕ => (neumannEigenvalue (windowLengthGenerated b) n : ℂ)) := by
  let _ : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  have ha : windowLeft b < windowLeft b + windowLengthGenerated b := by
    linarith [windowLengthGenerated_pos hb]
  have h : intervalNeumannSpectrum ha =
      Set.range (fun n : ℕ => (neumannEigenvalue (windowLengthGenerated b) n : ℂ)) :=
    intervalNeumannSpectrum_eq_range (windowLeft b) (windowLengthGenerated b)
  have heq := windowLeft_add_length hb
  generalize windowLeft b + windowLengthGenerated b = c at ha h heq
  subst c
  exact h

theorem generatedWindow_neumannResolvent_existsUnique {b : ℝ} (hb : 0 < b) (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue (windowLengthGenerated b) n : ℂ)) :
    ∃! S : ComplexIntervalL2 (windowLeft b) (windowRight b) →L[ℂ]
        ComplexIntervalL2 (windowLeft b) (windowRight b),
      IsIntervalNeumannResolvent (sub_pos.mp (windowLengthGenerated_pos hb)) z S ∧
        IsCompactOperator S := by
  obtain ⟨S, hS, huniq⟩ := intervalNeumannResolvent_existsUnique
    (sub_pos.mp (windowLengthGenerated_pos hb)) z hz
  exact ⟨S, ⟨hS, hS.isCompact⟩, fun T hT => huniq T hT.1⟩

/-- A complete basis and coefficient criterion on the original generated interval. -/
theorem generatedWindow_neumannBasis {b : ℝ} (hb : 0 < b) :
    ∃ B : HilbertBasis ℕ ℂ (ComplexIntervalL2 (windowLeft b) (windowRight b)),
      (∀ f : ComplexIntervalL2 (windowLeft b) (windowRight b),
        f ∈ complexNeumannDomain (windowLeft b) (windowRight b) ↔
          Summable (fun n : ℕ => (neumannEigenvalue (windowLengthGenerated b) n) ^ 2 *
            ‖inner ℂ (B n) f‖ ^ 2)) ∧
      (∀ f : complexNeumannDomain (windowLeft b) (windowRight b), ∀ n : ℕ,
        inner ℂ (B n) ((complexNeumannOperator
            (sub_pos.mp (windowLengthGenerated_pos hb))).toFun f) =
          (neumannEigenvalue (windowLengthGenerated b) n : ℂ) *
            inner ℂ (B n) (f : ComplexIntervalL2 (windowLeft b) (windowRight b))) := by
  let _ : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  have ha : windowLeft b < windowLeft b + windowLengthGenerated b := by
    linarith [windowLengthGenerated_pos hb]
  have h :
      ∃ B : HilbertBasis ℕ ℂ
          (ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b)),
        (∀ f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b),
          f ∈ complexNeumannDomain (windowLeft b) (windowLeft b + windowLengthGenerated b) ↔
            Summable (fun n : ℕ => (neumannEigenvalue (windowLengthGenerated b) n) ^ 2 *
              ‖inner ℂ (B n) f‖ ^ 2)) ∧
        (∀ f : complexNeumannDomain (windowLeft b) (windowLeft b + windowLengthGenerated b),
          ∀ n : ℕ, inner ℂ (B n) ((complexNeumannOperator ha).toFun f) =
            (neumannEigenvalue (windowLengthGenerated b) n : ℂ) *
              inner ℂ (B n)
                (f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b))) := by
    refine ⟨translatedNeumannCosineBasis (windowLeft b) (windowLengthGenerated b), ?_, ?_⟩
    · intro f
      simpa only [coe_translatedNeumannCosineBasis] using
        translatedNeumann_domain_iff (windowLeft b) (windowLengthGenerated b) f
    · intro f n
      simpa only [coe_translatedNeumannCosineBasis] using
        translatedNeumannOperator_coefficients (windowLeft b) (windowLengthGenerated b) f n
  have heq := windowLeft_add_length hb
  generalize windowLeft b + windowLengthGenerated b = c at ha h heq
  subst c
  exact h

theorem generatedWindow_neumannEigenvalue_formula {b : ℝ} (hb : 0 < b) (n : ℕ) :
    neumannEigenvalue (windowLengthGenerated b) n =
      ((n : ℝ) * Real.pi /
        (b * (Real.sqrt (2 * Real.pi) - Real.sqrt 2))) ^ 2 := by
  rw [neumannEigenvalue, windowLengthGenerated_eq,
    Correlation.Endpoints.windowLength_eq hb]

end GeneratedFoundations.Spectral
