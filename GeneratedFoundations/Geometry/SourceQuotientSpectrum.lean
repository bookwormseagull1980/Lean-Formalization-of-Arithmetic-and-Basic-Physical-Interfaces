module

public import GeneratedFoundations.Geometry.SourceQuotientCasimir
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Data.Finset.Sigma

/-!
# Spectrum and compact resolvents of the actual central quotient

The bounded inverses below act on the quotient Haar space and take values
in the full domain of its previously constructed differential closure.
Their two inverse identities determine the entire spectrum. Pullback
identifies each retained eigenspace with the corresponding complete source
matrix-coefficient block, including both matrix indices.

Compactness is proved by operator-norm approximation with finite sums of
rank-one maps. The uniform tail estimate uses the growing source energies;
no finite cutoff is imposed on the operator domain or on its spectrum.
-/

@[expose] public section

noncomputable section

open Filter InnerProductSpace
open scoped BigOperators Topology LinearPMap lp
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceQuotientCasimir
open GeneratedFoundations.Geometry.SourceCasimirClosure (energy energy_nonneg energy_strictMono)
open GeneratedFoundations.Geometry.SourceCasimirResolvent
  (inverseCoefficient inverseBound inverseBound_nonneg inverseCoefficient_le)
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceQuotientSpectrum

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The shifted map retains the complete closed differential domain. -/
def shifted (z : ℂ) : operator.domain →ₗ[ℂ] QuotientL2 :=
  operator.toFun - z • operator.domain.subtype

def inverseSequenceMap (z : ℂ) :
    lp (fun _ : EvenIndex => ℂ) 2 →L[ℂ] lp (fun _ : EvenIndex => ℂ) 2 :=
  lp.mapCLM 2
    (fun a : EvenIndex => inverseCoefficient z a.val.1 • ContinuousLinearMap.id ℂ ℂ)
    (inverseBound_nonneg z)
    (fun a => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        inverseCoefficient_le z a.val.1)

/-- The hypothesis excludes only retained energies; an odd source energy
is a legitimate resolvent point of the quotient. -/
def resolvent (z : ℂ) (_hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    QuotientL2 →L[ℂ] QuotientL2 :=
  quotientBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((inverseSequenceMap z).comp quotientBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_repr (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ))
    (f : QuotientL2) (a : EvenIndex) :
    quotientBasis.repr (resolvent z hz f) a =
      inverseCoefficient z a.val.1 * quotientBasis.repr f a := by
  change quotientBasis.repr
    (quotientBasis.repr.symm (inverseSequenceMap z (quotientBasis.repr f))) a = _
  rw [quotientBasis.repr.apply_symm_apply]
  rfl

theorem resolvent_coefficients (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ))
    (f : QuotientL2) (a : EvenIndex) :
    inner ℂ (quotientBasisVector a) (resolvent z hz f) =
      inverseCoefficient z a.val.1 * inner ℂ (quotientBasisVector a) f := by
  simpa only [HilbertBasis.repr_apply_apply, quotientBasis_apply] using
    resolvent_repr z hz f a

theorem resolvent_mem_domain (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ))
    (f : QuotientL2) : resolvent z hz f ∈ operator.domain := by
  apply (operator_domain_iff_memℓp _).mpr
  have heq : (fun a : EvenIndex => (energy a.val.1 : ℂ) *
      inner ℂ (quotientBasisVector a) (resolvent z hz f)) =
      (fun a => quotientBasis.repr (f + z • resolvent z hz f) a) := by
    funext a
    rw [HilbertBasis.repr_apply_apply, quotientBasis_apply, inner_add_right,
      inner_smul_right, resolvent_coefficients]
    have hden : (energy a.val.1 : ℂ) - z ≠ 0 :=
      sub_ne_zero.mpr (hz a.val.1 a.property).symm
    unfold inverseCoefficient
    field_simp [hden]
    ring
  rw [heq]
  exact lp.memℓp (quotientBasis.repr (f + z • resolvent z hz f))

theorem resolvent_right_inverse (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) (f : QuotientL2) :
    shifted z ⟨resolvent z hz f, resolvent_mem_domain z hz f⟩ = f := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  rw [quotientBasis_apply]
  change inner ℂ (quotientBasisVector a)
    (operator ⟨resolvent z hz f, resolvent_mem_domain z hz f⟩ - z • resolvent z hz f) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right, resolvent_coefficients]
  have hden : (energy a.val.1 : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (hz a.val.1 a.property).symm
  unfold inverseCoefficient
  field_simp [hden]

theorem resolvent_left_inverse (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) (u : operator.domain) :
    resolvent z hz (shifted z u) = (u : QuotientL2) := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  rw [quotientBasis_apply, resolvent_coefficients]
  change inverseCoefficient z a.val.1 *
    inner ℂ (quotientBasisVector a) (operator u - z • (u : QuotientL2)) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right]
  have hden : (energy a.val.1 : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (hz a.val.1 a.property).symm
  unfold inverseCoefficient
  field_simp [hden]

/-- Boundedness and both inverse identities refer to the actual full domain. -/
structure IsResolvent (z : ℂ) (S : QuotientL2 →L[ℂ] QuotientL2) : Prop where
  mem_domain : ∀ f, S f ∈ operator.domain
  right_inverse : ∀ f, shifted z ⟨S f, mem_domain f⟩ = f
  left_inverse : ∀ u : operator.domain, S (shifted z u) = (u : QuotientL2)

theorem resolvent_spec (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    IsResolvent z (resolvent z hz) where
  mem_domain := resolvent_mem_domain z hz
  right_inverse := resolvent_right_inverse z hz
  left_inverse := resolvent_left_inverse z hz

theorem IsResolvent.unique {z : ℂ} {S T : QuotientL2 →L[ℂ] QuotientL2}
    (hS : IsResolvent z S) (hT : IsResolvent z T) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    S f = S (shifted z ⟨T f, hT.mem_domain f⟩) := by rw [hT.right_inverse]
    _ = T f := hS.left_inverse ⟨T f, hT.mem_domain f⟩

theorem IsResolvent.not_eigenvalue {z : ℂ} {S : QuotientL2 →L[ℂ] QuotientL2}
    (hS : IsResolvent z S) (m : ℕ) (hm : Even m) : z ≠ (energy m : ℂ) := by
  intro hz
  subst z
  let a : EvenIndex := ⟨⟨m, 0, 0⟩, hm⟩
  let u : operator.domain := ⟨quotientBasisVector a, basis_mem_domain a⟩
  have hu : shifted (energy m : ℂ) u = 0 := by
    change operator ⟨quotientBasisVector a, basis_mem_domain a⟩ -
      (energy a.val.1 : ℂ) • quotientBasisVector a = 0
    rw [operator_basis, sub_self]
  have h := hS.left_inverse u
  rw [hu, map_zero] at h
  exact quotientBasisVector_orthonormal.ne_zero a h.symm

def resolventSet : Set ℂ := {z | ∃ S : QuotientL2 →L[ℂ] QuotientL2, IsResolvent z S}

/-- The spectrum is defined by failure of a bounded two-sided inverse,
not by listing the expected eigenvalues. -/
def spectrum : Set ℂ := resolventSetᶜ

theorem mem_resolventSet_iff (z : ℂ) :
    z ∈ resolventSet ↔ ∀ m : ℕ, Even m → z ≠ (energy m : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ m hm
    exact hS.not_eigenvalue m hm
  · intro hz
    exact ⟨resolvent z hz, resolvent_spec z hz⟩

/-- All spectral points are retained eigenvalues; no continuous or residual
spectral points have been left undecided. -/
theorem mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ↔ ∃ m : ℕ, Even m ∧ z = (energy m : ℂ) := by
  change (¬ z ∈ resolventSet) ↔ _
  simp only [mem_resolventSet_iff, not_forall, not_not, exists_prop]

theorem mem_spectrum_iff_even_degree (z : ℂ) :
    z ∈ spectrum ↔ ∃ n : ℕ, z = (energy (2 * n) : ℂ) := by
  rw [mem_spectrum_iff]
  constructor
  · rintro ⟨m, ⟨n, hn⟩, hz⟩
    exact ⟨n, by simpa only [hn, two_mul] using hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨2 * n, ⟨n, by omega⟩, hz⟩

theorem spectrum_eq_range : spectrum = Set.range (fun n : ℕ => (energy (2 * n) : ℂ)) := by
  ext z
  rw [mem_spectrum_iff_even_degree]
  exact exists_congr (fun _ => eq_comm)

theorem mem_spectrum_iff_round_index (z : ℂ) :
    z ∈ spectrum ↔ ∃ n : ℕ, z = (((2 * (n : ℝ) + 1) ^ 2 - 1 : ℝ) : ℂ) := by
  simp only [mem_spectrum_iff_even_degree, even_energy]

/-- Whenever the original source resolvent exists, the quotient inverse is
its restriction under the genuine Haar pullback. -/
theorem pullback_resolvent (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (f : QuotientL2) :
    pullbackL2 (resolvent z (fun m _ => hz m) f) =
      SourceCasimirResolvent.resolvent z hz (pullbackL2 f) := by
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  intro a
  rw [SourceCasimirResolvent.resolvent_coefficients]
  rcases Nat.even_or_odd a.1 with ha | ha
  · rw [← quotientBasisVector_inner ⟨a, ha⟩,
      ← quotientBasisVector_inner ⟨a, ha⟩, resolvent_coefficients]
  · rw [← coefficients_apply, pullbackL2_odd_coefficients _ a ha,
      ← coefficients_apply, pullbackL2_odd_coefficients _ a ha, mul_zero]

def eigenspace (z : ℂ) : Submodule ℂ QuotientL2 :=
  (LinearMap.ker (shifted z)).map operator.domain.subtype

theorem mem_eigenspace_iff (z : ℂ) (f : QuotientL2) :
    f ∈ eigenspace z ↔
      ∃ u : operator.domain, operator u = z • (u : QuotientL2) ∧ (u : QuotientL2) = f := by
  constructor
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩

/-- The full-domain intertwining identifies genuine eigenspaces. -/
theorem mem_eigenspace_pullback_iff (z : ℂ) (f : QuotientL2) :
    f ∈ eigenspace z ↔ pullbackL2 f ∈ SourceCasimirClosure.eigenspace z := by
  constructor
  · intro hf
    obtain ⟨u, hu, rfl⟩ := (mem_eigenspace_iff z f).mp hf
    apply (SourceCasimirClosure.mem_eigenspace_iff _ _).mpr
    refine ⟨⟨pullbackL2 (u : QuotientL2), pullback_mem_domain u⟩, ?_, rfl⟩
    rw [← pullback_operator, hu, map_smul]
  · intro hf
    obtain ⟨u, hu, huf⟩ := (SourceCasimirClosure.mem_eigenspace_iff _ _).mp hf
    have hp : pullbackL2 f ∈ SourceCasimirClosure.operator.domain := huf ▸ u.property
    let v : operator.domain := ⟨f, mem_domain_of_pullback f hp⟩
    apply (mem_eigenspace_iff z f).mpr
    refine ⟨v, ?_, rfl⟩
    apply pullbackL2.injective
    rw [pullback_operator, map_smul]
    have huv : (⟨pullbackL2 (v : QuotientL2), pullback_mem_domain v⟩ :
        SourceCasimirClosure.operator.domain) = u := Subtype.ext huf.symm
    rw [huv, hu, huf]

theorem eigenspace_map_pullback (m : ℕ) (hm : Even m) :
    (eigenspace (energy m : ℂ)).map pullbackL2.toLinearMap =
      SourceCasimirClosure.eigenspace (energy m : ℂ) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact (mem_eigenspace_pullback_iff _ f).mp hf
  · intro f hf
    have hb : f ∈ blockSpace m := by
      simpa only [SourceCasimirClosure.eigenspace_eq_blockSpace] using hf
    obtain ⟨g, hg, _⟩ := quotientClass_existsUnique f (averageL2_block_even hm hb)
    refine ⟨g, (mem_eigenspace_pullback_iff _ g).mpr ?_, hg⟩
    simpa only [hg] using hf

/-- Every row and column of the even source block descends. -/
def quotientBlockSpace (m : ℕ) (hm : Even m) : Submodule ℂ QuotientL2 :=
  Submodule.span ℂ (Set.range (fun ij : Fin (m + 1) × Fin (m + 1) =>
    quotientBasisVector ⟨⟨m, ij⟩, hm⟩))

theorem quotientBlockSpace_map_pullback (m : ℕ) (hm : Even m) :
    (quotientBlockSpace m hm).map pullbackL2.toLinearMap = blockSpace m := by
  simp only [quotientBlockSpace, blockSpace, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, LinearIsometry.coe_toLinearMap, pullbackL2_basisVector]

theorem eigenspace_eq_quotientBlockSpace (m : ℕ) (hm : Even m) :
    eigenspace (energy m : ℂ) = quotientBlockSpace m hm := by
  apply Submodule.map_injective_of_injective pullbackL2.injective
  rw [eigenspace_map_pullback m hm, quotientBlockSpace_map_pullback m hm,
    SourceCasimirClosure.eigenspace_eq_blockSpace]

/-- The equivalence is the actual pullback, with no arbitrary choice of a
vector-space isomorphism based only on dimension. -/
def eigenspaceEquiv (m : ℕ) (hm : Even m) :
    eigenspace (energy m : ℂ) ≃ₗ[ℂ] SourceCasimirClosure.eigenspace (energy m : ℂ) :=
  (Submodule.equivMapOfInjective pullbackL2.toLinearMap pullbackL2.injective
    (eigenspace (energy m : ℂ))).trans
      (LinearEquiv.ofEq _ _ (eigenspace_map_pullback m hm))

theorem eigenspace_finrank (m : ℕ) (hm : Even m) :
    Module.finrank ℂ (eigenspace (energy m : ℂ)) = (m + 1) ^ 2 := by
  rw [(eigenspaceEquiv m hm).finrank_eq, SourceCasimirClosure.eigenspace_finrank]

theorem eigenspace_even_finrank (n : ℕ) :
    Module.finrank ℂ (eigenspace (energy (2 * n) : ℂ)) = (2 * n + 1) ^ 2 :=
  eigenspace_finrank (2 * n) ⟨n, by omega⟩

theorem eigenspace_finite (m : ℕ) (hm : Even m) :
    FiniteDimensional ℂ (eigenspace (energy m : ℂ)) := by
  rw [eigenspace_eq_quotientBlockSpace m hm]
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun ij : Fin (m + 1) × Fin (m + 1) =>
      quotientBasisVector ⟨⟨m, ij⟩, hm⟩))

theorem eigenspace_eq_bot (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    eigenspace z = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  apply (Submodule.mem_bot ℂ).mpr
  by_contra hne
  obtain ⟨u, hu, rfl⟩ := (mem_eigenspace_iff z f).mp hf
  obtain ⟨m, hm, he⟩ := (SourceQuotientCasimir.eigenvalue_iff z).mp ⟨u, hne, hu⟩
  exact hz m hm he

theorem odd_eigenspace_eq_bot (m : ℕ) (hm : Odd m) : eigenspace (energy m : ℂ) = ⊥ := by
  apply eigenspace_eq_bot
  intro n hn he
  have hmn : m = n := energy_strictMono.injective (Complex.ofReal_injective he)
  exact (Nat.not_even_iff_odd.mpr hm) (hmn.symm ▸ hn)

private theorem inverseCoefficient_tail (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ‖inverseCoefficient z m‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ + ε⁻¹)
  refine ⟨N, fun m hm => ?_⟩
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hgrowth : (m : ℝ) ≤ energy m := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    unfold energy
    nlinarith [sq_nonneg (m : ℝ)]
  have hsub : energy m - ‖z‖ ≤ ‖(energy m : ℂ) - z‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg m)] using
      norm_sub_norm_le (energy m : ℂ) z
  have hlarge : ε⁻¹ ≤ ‖(energy m : ℂ) - z‖ := by linarith
  rw [inverseCoefficient, norm_inv]
  simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hε) hlarge

/-- The finite cutoff retains every matrix entry below its degree bound. -/
def cutoff (N : ℕ) : Finset EvenIndex := by
  classical
  exact ((Finset.range N).sigma (fun m =>
    (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))))).subtype (fun a => Even a.1)

@[simp] theorem mem_cutoff (N : ℕ) (a : EvenIndex) : a ∈ cutoff N ↔ a.val.1 < N := by
  classical
  simp [cutoff]

def resolventTruncation (z : ℂ) (N : ℕ) : QuotientL2 →L[ℂ] QuotientL2 :=
  ∑ a ∈ cutoff N, inverseCoefficient z a.val.1 •
    rankOne ℂ (quotientBasisVector a) (quotientBasisVector a)

theorem resolventTruncation_coefficients (z : ℂ) (N : ℕ) (f : QuotientL2) (a : EvenIndex) :
    inner ℂ (quotientBasisVector a) (resolventTruncation z N f) =
      if a ∈ cutoff N then
        inverseCoefficient z a.val.1 * inner ℂ (quotientBasisVector a) f else 0 := by
  classical
  simp [resolventTruncation, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp quotientBasisVector_orthonormal, mul_ite]

theorem resolventTruncation_isCompact (z : ℂ) (N : ℕ) :
    IsCompactOperator (resolventTruncation z N) := by
  let K := compactOperator (RingHom.id ℂ) QuotientL2 QuotientL2
  apply K.sum_mem
  intro a _ha
  have h : IsCompactOperator (rankOne ℂ (quotientBasisVector a) (quotientBasisVector a)) := by
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (quotientBasisVector a))).comp_clm
        (innerSL ℂ (quotientBasisVector a))
  exact h.smul (inverseCoefficient z a.val.1)

private theorem diagonal_norm_le (T : QuotientL2 →L[ℂ] QuotientL2)
    (c : EvenIndex → ℂ)
    (hT : ∀ f a, inner ℂ (quotientBasisVector a) (T f) =
      c a * inner ℂ (quotientBasisVector a) f)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro f
  have hmono : ‖quotientBasis.repr (T f)‖ ≤ ‖(C : ℂ) • quotientBasis.repr f‖ := by
    apply lp.norm_mono (by norm_num)
    intro a
    simp only [HilbertBasis.repr_apply_apply, quotientBasis_apply, hT,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hc a) (norm_nonneg _)
  simpa only [quotientBasis.repr.norm_map, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hC] using hmono

theorem resolventTruncation_norm_sub_le (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) (N : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htail : ∀ m : ℕ, N ≤ m → ‖inverseCoefficient z m‖ ≤ ε) :
    ‖resolventTruncation z N - resolvent z hz‖ ≤ ε := by
  classical
  refine diagonal_norm_le _
    (fun a => if a ∈ cutoff N then 0 else -inverseCoefficient z a.val.1) ?_ ε hε ?_
  · intro f a
    rw [sub_apply, inner_sub_right,
      resolventTruncation_coefficients, resolvent_coefficients]
    by_cases ha : a ∈ cutoff N <;> simp [ha]
  · intro a
    by_cases ha : a ∈ cutoff N
    · simpa only [ite_eq_left ha, norm_zero] using hε
    · rw [ite_eq_right ha, norm_neg]
      exact htail a.val.1 (Nat.le_of_not_gt (by simpa only [mem_cutoff] using ha))

theorem resolventTruncation_tendsto (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    Tendsto (resolventTruncation z) atTop (𝓝 (resolvent z hz)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := inverseCoefficient_tail z (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (resolventTruncation_norm_sub_le z hz n (ε / 2) (half_pos hε).le
    (fun m hm => hN m (hn.trans hm))).trans_lt (half_lt_self hε)

/-- Compactness holds for every bounded inverse, including the resolvent
points that are eigenvalues of the unquotiented source operator. -/
theorem resolvent_isCompact (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    IsCompactOperator (resolvent z hz) :=
  isCompactOperator_of_tendsto (resolventTruncation_tendsto z hz)
    (Eventually.of_forall (resolventTruncation_isCompact z))

theorem IsResolvent.isCompact {z : ℂ} {S : QuotientL2 →L[ℂ] QuotientL2}
    (hS : IsResolvent z S) : IsCompactOperator S := by
  have hz := hS.not_eigenvalue
  rw [hS.unique (resolvent_spec z hz)]
  exact resolvent_isCompact z hz

theorem resolvent_existsUnique (z : ℂ) (hz : ∀ m : ℕ, Even m → z ≠ (energy m : ℂ)) :
    ∃! S : QuotientL2 →L[ℂ] QuotientL2, IsResolvent z S := by
  refine ⟨resolvent z hz, resolvent_spec z hz, ?_⟩
  intro S hS
  exact hS.unique (resolvent_spec z hz)

theorem has_compact_resolvent :
    ∃ S : QuotientL2 →L[ℂ] QuotientL2, IsResolvent (-1) S ∧ IsCompactOperator S := by
  have hz : ∀ m : ℕ, Even m → (-1 : ℂ) ≠ (energy m : ℂ) := by
    intro m _ he
    have hre := congrArg Complex.re he
    have hm := energy_nonneg m
    norm_num at hre
    linarith
  exact ⟨resolvent (-1) hz, resolvent_spec (-1) hz, resolvent_isCompact (-1) hz⟩

end GeneratedFoundations.Geometry.SourceQuotientSpectrum
