module

public import GeneratedFoundations.Spectral.NeumannSpectrum
public import GeneratedFoundations.Spectral.NeumannCanonicalModes
public import GeneratedFoundations.Spectral.NeumannHeatSemigroup
public import Mathlib.LinearAlgebra.Trace

/-!
# Spectral projections and the intrinsic response order

The carrier is the class of nonzero orthogonal projections onto eigenspaces
at points of the spectrum of the original Neumann differential operator.
No integer enumeration enters its definition. The complete spectrum and
eigenline theorems classify this class by the actual cosine projections.
Heat response is the ordinary finite-dimensional trace on each projection
range; no trace of an infinite-dimensional endomorphism is used.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap NNReal ComplexConjugate
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.NeumannSpectralProjections

variable (L : ℝ) [hL : Fact (0 < L)]

abbrev Hilbert := ComplexIntervalL2 0 L
abbrev End := Hilbert L →L[ℂ] Hilbert L

/-- The eigenspace retains the domain of the original unbounded operator. -/
def eigenspace (z : ℂ) : Submodule ℂ (Hilbert L) :=
  (LinearMap.ker (neumannShift L z)).map (complexNeumannOperator hL.out).domain.subtype

theorem mem_eigenspace_iff (z : ℂ) (f : Hilbert L) :
    f ∈ eigenspace L z ↔ ∃ u : (complexNeumannOperator hL.out).domain,
      complexNeumannOperator hL.out u = z • (u : Hilbert L) ∧ (u : Hilbert L) = f := by
  constructor
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, neumannShift_apply, sub_eq_zero] using hu, huf⟩
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, neumannShift_apply, sub_eq_zero] using hu, huf⟩

theorem eigenspace_eq_span (n : ℕ) :
    eigenspace L (neumannEigenvalue L n : ℂ) =
      Submodule.span ℂ {neumannCosineMode L n} := by
  ext f
  rw [mem_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, hc⟩ := (complexNeumann_eigenvector_iff L n u).mp hu
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • neumannCosineDomainVector L n, ?_, rfl⟩
    apply (complexNeumann_eigenvector_iff L n _).mpr
    exact ⟨c, rfl⟩

def cosineProjection (n : ℕ) : End L :=
  rankOne ℂ (neumannCosineMode L n) (neumannCosineMode L n)

theorem cosineProjection_apply (n : ℕ) (f : Hilbert L) :
    cosineProjection L n f = inner ℂ (neumannCosineMode L n) f • neumannCosineMode L n :=
  rankOne_apply _ _ _

theorem cosineProjection_orthogonal (n : ℕ) : IsStarProjection (cosineProjection L n) :=
  isStarProjection_rankOne_self ((neumannCosineMode_orthonormal L).norm_eq_one n)

@[simp]
theorem cosineProjection_self (n : ℕ) :
    cosineProjection L n (neumannCosineMode L n) = neumannCosineMode L n := by
  rw [cosineProjection_apply, orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L)]
  simp

theorem cosineProjection_ne_zero (n : ℕ) : cosineProjection L n ≠ 0 := by
  intro hn
  have hh := cosineProjection_self L n
  rw [hn, zero_apply] at hh
  exact (neumannCosineMode_orthonormal L).ne_zero n hh.symm

theorem cosineProjection_range (n : ℕ) :
    (cosineProjection L n).range = Submodule.span ℂ {neumannCosineMode L n} := by
  ext f
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨inner ℂ (neumannCosineMode L n) g, (cosineProjection_apply L n g).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • neumannCosineMode L n, ?_⟩
    change cosineProjection L n (c • neumannCosineMode L n) = _
    rw [map_smul, cosineProjection_self]

theorem cosineProjection_eigenspace (n : ℕ) :
    (cosineProjection L n).range = eigenspace L (neumannEigenvalue L n : ℂ) := by
  rw [cosineProjection_range, eigenspace_eq_span]

theorem cosineProjection_mul_of_ne {m n : ℕ} (hmn : m ≠ n) :
    cosineProjection L m * cosineProjection L n = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  simp [cosineProjection_apply,
    orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) m n, hmn]

theorem cosineProjection_resolution (f : Hilbert L) :
    HasSum (fun n => cosineProjection L n f) f := by
  simpa only [cosineProjection_apply] using neumannCosineBasis_hasSum L f

/-- The quantifier is over the actual spectrum and original eigenspaces,
not over a previously chosen list of labels. -/
structure IsSpectralProjection (P : End L) : Prop where
  orthogonal : IsStarProjection P
  nonzero : P ≠ 0
  spectral_range : ∃ z ∈ neumannSpectrum L, P.range = eigenspace L z

theorem cosineProjection_spectral (n : ℕ) : IsSpectralProjection L (cosineProjection L n) :=
  ⟨cosineProjection_orthogonal L n, cosineProjection_ne_zero L n,
    (neumannEigenvalue L n : ℂ), (mem_neumannSpectrum_iff L _).mpr ⟨n, rfl⟩,
    cosineProjection_eigenspace L n⟩

theorem spectralProjection_classification (P : End L) (hP : IsSpectralProjection L P) :
    ∃ n : ℕ, P = cosineProjection L n := by
  obtain ⟨z, hz, hrange⟩ := hP.spectral_range
  obtain ⟨n, rfl⟩ := (mem_neumannSpectrum_iff L z).mp hz
  exact ⟨n, ContinuousLinearMap.IsStarProjection.ext hP.orthogonal
    (cosineProjection_orthogonal L n)
    (hrange.trans (cosineProjection_eigenspace L n).symm)⟩

theorem cosineProjection_injective : Function.Injective (cosineProjection L) := by
  intro m n heq
  by_contra hmn
  have hzero := cosineProjection_mul_of_ne L hmn
  rw [heq, (cosineProjection_orthogonal L n).isIdempotentElem.eq] at hzero
  exact cosineProjection_ne_zero L n hzero

theorem spectralProjection_existsUnique (P : End L) (hP : IsSpectralProjection L P) :
    ∃! n : ℕ, P = cosineProjection L n := by
  obtain ⟨n, hn⟩ := spectralProjection_classification L P hP
  exact ⟨n, hn, fun m hm => cosineProjection_injective L (hm.symm.trans hn)⟩

def Component := {P : End L // IsSpectralProjection L P}

def mode (n : ℕ) : Component L := ⟨cosineProjection L n, cosineProjection_spectral L n⟩

theorem mode_bijective : Function.Bijective (mode L) := by
  constructor
  · intro m n heq
    exact cosineProjection_injective L (congrArg Subtype.val heq)
  · intro P
    obtain ⟨n, hn⟩ := spectralProjection_classification L P.val P.property
    exact ⟨n, Subtype.ext hn.symm⟩

/-- This equivalence records the proved classification of the intrinsic class. -/
def enumeration : ℕ ≃ Component L := Equiv.ofBijective (mode L) (mode_bijective L)

def coordinate (P : Component L) : ℕ := (enumeration L).symm P

@[simp] theorem enumeration_apply (n : ℕ) : enumeration L n = mode L n := rfl

@[simp] theorem coordinate_mode (n : ℕ) : coordinate L (mode L n) = n :=
  (enumeration L).symm_apply_apply n

@[simp] theorem mode_coordinate (P : Component L) : mode L (coordinate L P) = P :=
  (enumeration L).apply_symm_apply P

def energy (P : Component L) : ℝ := neumannEigenvalue L (coordinate L P)

theorem component_range (P : Component L) :
    P.val.range = Submodule.span ℂ {neumannCosineMode L (coordinate L P)} := by
  have hp := congrArg Subtype.val (mode_coordinate L P)
  rw [← hp]
  exact cosineProjection_range L _

instance componentRange_finite (P : Component L) : FiniteDimensional ℂ P.val.range := by
  rw [component_range]
  infer_instance

theorem component_rank_one (P : Component L) : Module.finrank ℂ P.val.range = 1 := by
  rw [component_range]
  exact finrank_span_singleton ((neumannCosineMode_orthonormal L).ne_zero _)

theorem component_eigenspace (P : Component L) : P.val.range = eigenspace L (energy L P : ℂ) := by
  rw [component_range, energy, eigenspace_eq_span]

theorem heat_on_range (P : Component L) (t : ℝ≥0) (f : P.val.range) :
    NeumannHeatSemigroup.heat L t (f : Hilbert L) =
      (NeumannHeatSemigroup.decay L t (coordinate L P) : ℂ) • (f : Hilbert L) := by
  have hf := (le_of_eq (component_range L P)) f.property
  rw [Submodule.mem_span_singleton] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc, map_smul, NeumannHeatSemigroup.heat_cosine, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

def restrictedHeat (P : Component L) (t : ℝ≥0) : P.val.range →ₗ[ℂ] P.val.range where
  toFun f := ⟨NeumannHeatSemigroup.heat L t f, by
    rw [heat_on_range]
    exact P.val.range.smul_mem _ f.property⟩
  map_add' f g := Subtype.ext ((NeumannHeatSemigroup.heat L t).map_add f g)
  map_smul' c f := Subtype.ext ((NeumannHeatSemigroup.heat L t).map_smul c f)

theorem restrictedHeat_scalar (P : Component L) (t : ℝ≥0) :
    restrictedHeat L P t = (NeumannHeatSemigroup.decay L t (coordinate L P) : ℂ) •
      (LinearMap.id : P.val.range →ₗ[ℂ] P.val.range) := by
  apply LinearMap.ext
  intro f
  exact Subtype.ext (heat_on_range L P t f)

/-- The trace is taken on the proved one-dimensional eigenspace. -/
theorem restrictedHeat_trace (P : Component L) (t : ℝ≥0) :
    LinearMap.trace ℂ P.val.range (restrictedHeat L P t) =
      (Real.exp (-(t : ℝ) * energy L P / 2) : ℂ) := by
  rw [restrictedHeat_scalar, map_smul, LinearMap.trace_id, component_rank_one]
  simp only [Nat.cast_one, smul_eq_mul, mul_one]
  rfl

def response (P : Component L) (t : ℝ≥0) : ℝ :=
  (LinearMap.trace ℂ P.val.range (restrictedHeat L P t)).re

theorem response_eq (P : Component L) (t : ℝ≥0) :
    response L P t = Real.exp (-(t : ℝ) * energy L P / 2) := by
  simp only [response, restrictedHeat_trace, Complex.ofReal_re]

@[simp]
theorem response_mode (n : ℕ) (t : ℝ≥0) :
    response L (mode L n) t = NeumannHeatSemigroup.decay L t n := by
  simp only [response_eq, energy, coordinate_mode, NeumannHeatSemigroup.decay]

theorem response_pos (P : Component L) (t : ℝ≥0) : 0 < response L P t := by
  rw [response_eq]
  exact Real.exp_pos _

theorem response_le_response_iff (P Q : Component L) {t : ℝ≥0} (ht : 0 < t) :
    response L P t ≤ response L Q t ↔ coordinate L Q ≤ coordinate L P := by
  have ht' : 0 < (t : ℝ) := ht
  rw [response_eq, response_eq, Real.exp_le_exp]
  have hh : -(t : ℝ) * energy L P / 2 ≤ -(t : ℝ) * energy L Q / 2 ↔
      energy L Q ≤ energy L P := by constructor <;> intro h <;> nlinarith
  exact hh.trans (neumannEigenvalue_strictMono L).le_iff_le

theorem response_lt_response_iff (P Q : Component L) {t : ℝ≥0} (ht : 0 < t) :
    response L P t < response L Q t ↔ coordinate L Q < coordinate L P := by
  have ht' : 0 < (t : ℝ) := ht
  rw [response_eq, response_eq, Real.exp_lt_exp]
  have hh : -(t : ℝ) * energy L P / 2 < -(t : ℝ) * energy L Q / 2 ↔
      energy L Q < energy L P := by constructor <;> intro h <;> nlinarith
  exact hh.trans (neumannEigenvalue_strictMono L).lt_iff_lt

theorem response_injective {t : ℝ≥0} (ht : 0 < t) :
    Function.Injective (fun P : Component L => response L P t) := by
  intro P Q h
  apply (enumeration L).symm.injective
  exact le_antisymm ((response_le_response_iff L Q P ht).mp h.ge)
    ((response_le_response_iff L P Q ht).mp h.le)

/-- Larger retained heat response precedes smaller response. The parameter `1`
is only used to package the order; every strictly positive parameter gives it. -/
instance componentLinearOrder : LinearOrder (Component L) :=
  LinearOrder.lift' (fun P => -response L P 1)
    (neg_injective.comp (response_injective L (by norm_num)))

theorem component_le_iff (P Q : Component L) :
    P ≤ Q ↔ coordinate L P ≤ coordinate L Q := by
  change -response L P 1 ≤ -response L Q 1 ↔ _
  rw [neg_le_neg_iff, response_le_response_iff L Q P (by norm_num)]

theorem component_lt_iff (P Q : Component L) :
    P < Q ↔ coordinate L P < coordinate L Q := by
  change -response L P 1 < -response L Q 1 ↔ _
  rw [neg_lt_neg_iff, response_lt_response_iff L Q P (by norm_num)]

theorem response_order_time_independent (P Q : Component L) {t : ℝ≥0} (ht : 0 < t) :
    P < Q ↔ response L Q t < response L P t := by
  rw [component_lt_iff, response_lt_response_iff L Q P ht]

theorem response_weak_order_time_independent (P Q : Component L) {t : ℝ≥0}
    (ht : 0 < t) : P ≤ Q ↔ response L Q t ≤ response L P t := by
  rw [component_le_iff, response_le_response_iff L Q P ht]

theorem energy_order (P Q : Component L) : P < Q ↔ energy L P < energy L Q := by
  rw [component_lt_iff]
  exact (neumannEigenvalue_strictMono L).lt_iff_lt.symm

/-- The order type of the original spectral projection class is `ω`. -/
def enumerationOrderIso : ℕ ≃o Component L where
  toEquiv := enumeration L
  map_rel_iff' := by
    intro m n
    change mode L m ≤ mode L n ↔ m ≤ n
    rw [component_le_iff, coordinate_mode, coordinate_mode]

def orderCoordinate : Component L ≃o ℕ := (enumerationOrderIso L).symm

@[simp] theorem orderCoordinate_apply (P : Component L) :
    orderCoordinate L P = coordinate L P := rfl

theorem component_wellFounded : WellFounded ((· < ·) : Component L → Component L → Prop) :=
  (orderCoordinate L).toOrderEmbedding.wellFounded Nat.lt_wfRel.wf

instance componentWellFoundedLT : WellFoundedLT (Component L) := component_wellFounded L

theorem mode_zero_le (P : Component L) : mode L 0 ≤ P := by
  rw [component_le_iff, coordinate_mode]
  exact Nat.zero_le _

theorem finite_initial_segment (P : Component L) : Set.Finite {Q : Component L | Q < P} := by
  have heq : {Q : Component L | Q < P} =
      coordinate L ⁻¹' {n : ℕ | n < coordinate L P} := by
    ext Q
    exact component_lt_iff L Q P
  rw [heq]
  exact (Set.finite_lt_nat (coordinate L P)).preimage
    (enumeration L).symm.injective.injOn

/-- A natural-number order coordinate is forced, rather than selected. -/
theorem orderCoordinate_unique (c : Component L ≃o ℕ) : c = orderCoordinate L := by
  let a : ℕ ≃o ℕ := (enumerationOrderIso L).trans c
  have ha (n : ℕ) : a n = n := by
    apply le_antisymm
    · simpa only [id_eq, a.apply_symm_apply] using a.monotone (a.symm.strictMono.id_le n)
    · exact a.strictMono.id_le n
  apply OrderIso.ext
  funext P
  have hh := ha (coordinate L P)
  change c (mode L (coordinate L P)) = coordinate L P at hh
  simpa only [mode_coordinate, orderCoordinate_apply] using hh

theorem orderCoordinate_existsUnique : ∃! _c : Component L ≃o ℕ, True :=
  ⟨orderCoordinate L, trivial, fun c _ => orderCoordinate_unique L c⟩

theorem enumerationOrderIso_unique (c : ℕ ≃o Component L) : c = enumerationOrderIso L :=
  congrArg (fun e : Component L ≃o ℕ => e.symm) (orderCoordinate_unique L c.symm)

def successor (P : Component L) : Component L := mode L (coordinate L P + 1)

@[simp] theorem coordinate_successor (P : Component L) :
    coordinate L (successor L P) = coordinate L P + 1 := coordinate_mode L _

theorem successor_spec (P : Component L) :
    P < successor L P ∧ ∀ Q : Component L, P < Q → successor L P ≤ Q := by
  constructor
  · rw [component_lt_iff, coordinate_successor]
    exact Nat.lt_succ_self _
  · intro Q hQ
    rw [component_le_iff, coordinate_successor]
    exact Nat.succ_le_iff.mpr ((component_lt_iff L P Q).mp hQ)

/-- Every member has exactly one immediate successor, stated entirely in
the response order on the intrinsic projection class. -/
theorem immediate_successor_existsUnique (P : Component L) :
    ∃! Q : Component L, P < Q ∧ ∀ R : Component L, P < R → Q ≤ R := by
  refine ⟨successor L P, successor_spec L P, ?_⟩
  intro Q hQ
  exact le_antisymm (hQ.2 _ (successor_spec L P).1) ((successor_spec L P).2 Q hQ.1)

theorem energy_nonneg (P : Component L) : 0 ≤ energy L P :=
  neumannEigenvalue_nonneg L _

theorem energy_eq_zero_iff (P : Component L) : energy L P = 0 ↔ P = mode L 0 := by
  constructor
  · intro h
    have hn : coordinate L P = 0 := (neumannEigenvalue_strictMono L).injective
      (h.trans (neumannEigenvalue_zero L).symm)
    simpa only [hn] using (mode_coordinate L P).symm
  · rintro rfl
    simp only [energy, coordinate_mode, neumannEigenvalue_zero]

theorem zero_energy_existsUnique : ∃! P : Component L, energy L P = 0 := by
  exact ⟨mode L 0, (energy_eq_zero_iff L _).mpr rfl,
    fun P h => (energy_eq_zero_iff L P).mp h⟩

theorem domain_mem_range_iff (P : Component L)
    (f : (complexNeumannOperator hL.out).domain) :
    (f : Hilbert L) ∈ P.val.range ↔
      complexNeumannOperator hL.out f = (energy L P : ℂ) • (f : Hilbert L) := by
  have hr := component_range L P
  constructor
  · intro hf
    have hh := (le_of_eq hr) hf
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hh
    exact (complexNeumann_eigenvector_iff L (coordinate L P) f).mpr ⟨c, hc.symm⟩
  · intro hf
    obtain ⟨c, hc⟩ := (complexNeumann_eigenvector_iff L (coordinate L P) f).mp hf
    exact (le_of_eq hr.symm) (Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩)

/-- Fixing unit norm and a positive real left endpoint removes exactly the
phase ambiguity in every original spectral line. -/
theorem canonical_representative_existsUnique (P : Component L) :
    ∃! f : (complexNeumannOperator hL.out).domain,
      (f : Hilbert L) ∈ P.val.range ∧ ‖(f : Hilbert L)‖ = 1 ∧
      ∃ r : ℝ, 0 < r ∧ neumannLeftTrace L f = (r : ℂ) := by
  simpa only [domain_mem_range_iff, energy] using
    neumannCanonicalMode_existsUnique L (coordinate L P)

theorem energy_coordinate_certification (P : Component L) :
    energy L P = (coordinate L P : ℝ) ^ 2 * neumannEigenvalue L 1 := by
  simp only [energy, neumannEigenvalue, Nat.cast_one, one_mul]
  ring

/-- The finite-dimensional trace agrees with the survival response of
every unit representative in the same eigenspace. -/
theorem response_eq_unit_inner (P : Component L) (t : ℝ≥0) (f : P.val.range)
    (hf : ‖(f : Hilbert L)‖ = 1) :
    inner ℂ (f : Hilbert L) (NeumannHeatSemigroup.heat L t f) = (response L P t : ℂ) := by
  rw [heat_on_range, inner_smul_right, inner_self_eq_norm_sq_to_K, hf]
  simp only [RCLike.ofReal_one, one_pow, mul_one, response_eq]
  rfl

theorem response_log_ratio (P Q : Component L) (t : ℝ≥0) :
    Real.log (response L P t / response L Q t) =
      (t : ℝ) * ((energy L Q - energy L P) / 2) := by
  rw [response_eq, response_eq, ← Real.exp_sub, Real.log_exp]
  ring

/-- Only nonnegative change parameters are passed to the heat semigroup.
Near a strictly positive parameter the clipping map is the identity, so the
derivative is that of the actual positive-parameter response ratio. -/
theorem response_log_ratio_hasDerivAt (P Q : Component L) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log
      (response L P s.toNNReal / response L Q s.toNNReal))
      ((energy L Q - energy L P) / 2) t := by
  have hd := (hasDerivAt_id t).mul_const ((energy L Q - energy L P) / 2)
  simp only [one_mul] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [response_log_ratio, Real.coe_toNNReal s hs.le]
  rfl

theorem response_log_ratio_derivative_pos (P Q : Component L) (hPQ : P < Q) :
    0 < (energy L Q - energy L P) / 2 := by
  exact div_pos (sub_pos.mpr ((energy_order L P Q).mp hPQ)) (by norm_num)

end GeneratedFoundations.Spectral.NeumannSpectralProjections
