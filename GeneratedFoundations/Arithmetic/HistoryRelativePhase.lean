module

public import GeneratedFoundations.Arithmetic.HistoryPhaseProjection
public import GeneratedFoundations.Arithmetic.HistoryRelativeCharge
public import GeneratedFoundations.Operations.FinitePhaseFlow

/-!
# Continuous relative phase of the actual invariant--detail decomposition

The primitive weights are computed from the traces of the two actual
orthogonal phase projections. They are `(-n,1)`, not prescribed physical
hypercharges. Their continuous action is constructed on the original full
complex coefficient space. Its generator, exponential and norm conservation
are proved together. The root-one detail space is allowed to vanish.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryRelativePhase

open HistoryModuleRepresentation HistoryPhaseProjection

def block (n : ℕ) : (ℂ × ℂ) →ₐ[ℂ] Module.End ℂ (Space n) where
  toFun z := z.1 • projection n + z.2 • HistoryPhaseProjection.residual n
  map_zero' := by simp
  map_one' := by simp [HistoryPhaseProjection.residual]
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; module
  map_mul' z w := by
    simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, projection_idempotent, residual_idempotent,
      projection_residual, residual_projection, smul_zero, add_zero, zero_add]
    congr 1 <;> rw [mul_comm]
  commutes' z := by
    change z • projection n + z • residual n = z • (1 : Module.End ℂ (Space n))
    rw [← smul_add]
    congr 1
    simp [HistoryPhaseProjection.residual]

@[simp] theorem block_apply (n : ℕ) (z : ℂ × ℂ) (x : Space n) :
    block n z x = z.1 • projection n x + z.2 • HistoryPhaseProjection.residual n x := rfl

def relative (n : ℕ) (a b : ℤ) : Module.End ℂ (Space n) := block n (a, b)

theorem relative_trace (n : ℕ) (a b : ℤ) :
    LinearMap.trace ℂ (Space n) (relative n a b) =
      (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) * ((a : ℂ) + n * b) := by
  change LinearMap.trace ℂ (Space n)
    ((a : ℂ) • projection n + (b : ℂ) • HistoryPhaseProjection.residual n) = _
  rw [map_add, map_smul, map_smul, projection_trace, residual_trace]
  change (a : ℂ) * _ + (b : ℂ) * (_ * _) = _
  ring

theorem relative_trace_zero_iff (n : ℕ) (a b : ℤ) :
    LinearMap.trace ℂ (Space n) (relative n a b) = 0 ↔ a + (n : ℤ) * b = 0 := by
  rw [relative_trace, mul_eq_zero]
  have hc : (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (CompleteHistory.History (n + 1)) ≠ 0)
  rw [or_iff_right hc]
  exact_mod_cast (Iff.rfl : (a : ℂ) + (n : ℂ) * (b : ℂ) = 0 ↔
    (a : ℂ) + (n : ℂ) * (b : ℂ) = 0)

def generator (n : ℕ) : Module.End ℂ (Space n) := relative n (-(n : ℤ)) 1

theorem generator_trace (n : ℕ) : LinearMap.trace ℂ (Space n) (generator n) = 0 := by
  apply (relative_trace_zero_iff n _ _).mpr
  ring

theorem generator_unique (n : ℕ) (a b : ℤ)
    (hp : HistoryRelativeCharge.PrimitivePair a b)
    (ht : LinearMap.trace ℂ (Space n) (relative n a b) = 0) (hb : 0 < b) :
    relative n a b = generator n := by
  rcases (HistoryRelativeCharge.primitive_traceFree_iff n a b).mp
    ⟨hp, (relative_trace_zero_iff n a b).mp ht⟩ with h | h
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · exfalso
    linarith [h.2]

def scalar (w t : ℝ) : ℂ :=
  Operations.FinitePhaseFlow.phase (fun _ : Unit => w) t ()

@[simp] theorem scalar_zero (w : ℝ) : scalar w 0 = 1 :=
  Operations.FinitePhaseFlow.phase_zero _ _

theorem scalar_add (w s t : ℝ) : scalar w (s + t) = scalar w s * scalar w t :=
  Operations.FinitePhaseFlow.phase_add _ _ _ _

@[simp] theorem scalar_norm (w t : ℝ) : ‖scalar w t‖ = 1 :=
  Operations.FinitePhaseFlow.phase_norm _ _ _

theorem scalar_conj_mul (w t : ℝ) : (starRingEnd ℂ) (scalar w t) * scalar w t = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq]

def flow (n : ℕ) (t : ℝ) : Module.End ℂ (Space n) :=
  block n (scalar (-(n : ℝ)) t, scalar 1 t)

@[simp] theorem flow_apply (n : ℕ) (t : ℝ) (x : Space n) :
    flow n t x = scalar (-(n : ℝ)) t • projection n x +
      scalar 1 t • HistoryPhaseProjection.residual n x := rfl

theorem flow_zero (n : ℕ) : flow n 0 = 1 := by
  simp only [flow, scalar_zero]
  exact (block n).map_one

theorem flow_add (n : ℕ) (s t : ℝ) : flow n (s + t) = flow n s * flow n t := by
  change block n (scalar (-(n : ℝ)) (s + t), scalar 1 (s + t)) =
    block n (scalar (-(n : ℝ)) s, scalar 1 s) *
      block n (scalar (-(n : ℝ)) t, scalar 1 t)
  rw [scalar_add, scalar_add]
  exact (block n).map_mul (scalar (-(n : ℝ)) s, scalar 1 s)
    (scalar (-(n : ℝ)) t, scalar 1 t)

theorem flow_inverse (n : ℕ) (t : ℝ) : flow n (-t) * flow n t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem mixed_inner_zero (n : ℕ) (x y : Space n) :
    inner ℂ (HistoryPhaseProjection.residual n x) (projection n y) = 0 :=
  inner_eq_zero_symm.mpr (projection_residual_inner n y x)

theorem flow_inner (n : ℕ) (t : ℝ) (x y : Space n) :
    inner ℂ (flow n t x) (flow n t y) = inner ℂ x y := by
  have hex : inner ℂ x y =
      inner ℂ (projection n x) (projection n y) +
        inner ℂ (HistoryPhaseProjection.residual n x) (HistoryPhaseProjection.residual n y) := by
    conv_lhs => rw [← full_reconstruction n x, ← full_reconstruction n y]
    simp only [inner_add_left, inner_add_right, projection_residual_inner,
      mixed_inner_zero, add_zero, zero_add]
  rw [flow_apply, flow_apply, hex]
  simp only [inner_add_left, inner_add_right, inner_smul_left (𝕜 := ℂ),
    inner_smul_right (𝕜 := ℂ), projection_residual_inner, mixed_inner_zero,
    mul_zero, zero_add, add_zero]
  calc
    _ = ((starRingEnd ℂ) (scalar (-(n : ℝ)) t) * scalar (-(n : ℝ)) t) *
        inner ℂ (projection n x) (projection n y) +
      ((starRingEnd ℂ) (scalar 1 t) * scalar 1 t) *
        inner ℂ (HistoryPhaseProjection.residual n x) (HistoryPhaseProjection.residual n y) := by ring
    _ = _ := by rw [scalar_conj_mul, scalar_conj_mul, one_mul, one_mul]

theorem flow_norm (n : ℕ) (t : ℝ) (x : Space n) : ‖flow n t x‖ = ‖x‖ := by
  have h := congrArg Complex.re (flow_inner n t x x)
  have hs : ‖flow n t x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq (𝕜 := ℂ)] using h
  nlinarith [norm_nonneg (flow n t x), norm_nonneg x]

theorem flow_continuous (n : ℕ) (x : Space n) : Continuous (fun t : ℝ => flow n t x) := by
  have hc (w : ℝ) : Continuous (fun t : ℝ => scalar w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (Operations.FinitePhaseFlow.phase_hasDerivAt (fun _ : Unit => w) t ()).continuousAt
  exact ((hc _).smul continuous_const).add ((hc _).smul continuous_const)

abbrev End (n : ℕ) := Space n →L[ℂ] Space n

local instance (n : ℕ) : NormedRing (End n) := ContinuousLinearMap.toNormedRing
local instance (n : ℕ) : NormedAlgebra ℂ (End n) := ContinuousLinearMap.toNormedAlgebra
local instance (n : ℕ) : IsTopologicalRing (End n) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

def continuousBlock (n : ℕ) : (ℂ × ℂ) →ₐ[ℂ] End n :=
  Operations.FinitePhaseFlow.continuousModel.toAlgHom.comp (block n)

theorem flow_eq_exp (n : ℕ) (t : ℝ) :
    Operations.FinitePhaseFlow.continuousModel (flow n t) =
      NormedSpace.exp ((Complex.I * (t : ℂ)) •
        Operations.FinitePhaseFlow.continuousModel (generator n)) := by
  have hc : Continuous (continuousBlock n) :=
    (continuousBlock n).toLinearMap.continuous_of_finiteDimensional
  have he := Operations.FinitePhaseFlow.map_exp (continuousBlock n) hc
    (Complex.I * (-(n : ℂ)) * (t : ℂ), Complex.I * (t : ℂ))
  have hp : NormedSpace.exp
      (Complex.I * (-(n : ℂ)) * (t : ℂ), Complex.I * (t : ℂ)) =
      (scalar (-(n : ℝ)) t, scalar 1 t) := by
    apply Prod.ext <;>
      simp [scalar, Operations.FinitePhaseFlow.phase, ← Complex.exp_eq_exp_ℂ]
  rw [hp] at he
  change Operations.FinitePhaseFlow.continuousModel (flow n t) =
    NormedSpace.exp (Operations.FinitePhaseFlow.continuousModel
      (block n (Complex.I * (-(n : ℂ)) * (t : ℂ), Complex.I * (t : ℂ)))) at he
  rw [he]
  congr 1
  rw [← map_smul]
  congr 1
  unfold generator relative
  rw [← map_smul]
  congr 1
  ext <;> simp
  ring

structure Conclusions : Prop where
  trace_zero : ∀ n, LinearMap.trace ℂ (Space n) (generator n) = 0
  unique_primitive_choice : ∀ n a b, HistoryRelativeCharge.PrimitivePair a b →
    LinearMap.trace ℂ (Space n) (relative n a b) = 0 → 0 < b →
      relative n a b = generator n
  group_law : ∀ n s t, flow n (s + t) = flow n s * flow n t
  full_pairing : ∀ n t (x y : Space n), inner ℂ (flow n t x) (flow n t y) = inner ℂ x y
  strong_continuity : ∀ n (x : Space n), Continuous (fun t : ℝ => flow n t x)
  actual_exponential : ∀ n t, Operations.FinitePhaseFlow.continuousModel (flow n t) =
    NormedSpace.exp ((Complex.I * (t : ℂ)) •
      Operations.FinitePhaseFlow.continuousModel (generator n))

theorem generated : Conclusions where
  trace_zero := generator_trace
  unique_primitive_choice := generator_unique
  group_law := flow_add
  full_pairing := flow_inner
  strong_continuity := flow_continuous
  actual_exponential := flow_eq_exp

end GeneratedFoundations.Arithmetic.HistoryRelativePhase
