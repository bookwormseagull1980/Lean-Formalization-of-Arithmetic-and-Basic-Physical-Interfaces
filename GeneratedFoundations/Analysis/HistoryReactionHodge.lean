module

public import GeneratedFoundations.Analysis.HistoryReactionComplex

/-!
# Orthogonal reduction of the actual history reaction complex

The conserved vector is the leaf charge of the retained history. Its
coefficient is obtained from the actual coefficient-space inner product.
This gives the orthogonal decomposition, distinct from the unit-anchored
primitive in `HistoryReactionComplex`. Both decompositions use the same
three-leg differential and the same complete Hessian. No cutoff-independent
gap is needed for the exact reduction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryReactionHodge

open HistoryReactionForm HistoryReactionOperator HistoryReactionKernel
open HistoryReactionComplex

theorem pair_add_right {N : ℕ} (f g h : Zero N) :
    pairZero f (g + h) = pairZero f g + pairZero f h := by
  simp [pairZero, mul_add, Finset.sum_add_distrib]

theorem pair_sub_right {N : ℕ} (f g h : Zero N) :
    pairZero f (g - h) = pairZero f g - pairZero f h := by
  simp [pairZero, mul_sub, Finset.sum_sub_distrib]

theorem pair_add_left {N : ℕ} (f g h : Zero N) :
    pairZero (f + g) h = pairZero f h + pairZero g h := by
  rw [pairZero_symm, pair_add_right, pairZero_symm h f, pairZero_symm h g]

theorem pair_equilibrium {N : ℕ} (f : Zero N) (q : ℝ) :
    pairZero f (equilibrium q) = pairZero f leafCharge * q := by
  simp only [pairZero, equilibrium, mul_assoc, Finset.sum_mul]

def chargeNormSq (N : ℕ) : ℝ := pairZero (leafCharge (N := N)) leafCharge

theorem chargeNormSq_pos {N : ℕ} (hN : 1 ≤ N) : 0 < chargeNormSq N := by
  apply Finset.sum_pos' (fun s _ => mul_self_nonneg (leafCharge s))
  refine ⟨unit hN, Finset.mem_univ _, ?_⟩
  have hu : leafCharge (unit hN) = (1 : ℝ) := by
    simpa only [equilibrium, mul_one] using equilibrium_unit hN (1 : ℝ)
  rw [hu]
  norm_num

def coefficient {N : ℕ} (f : Zero N) : ℝ := pairZero leafCharge f / chargeNormSq N

def harmonic {N : ℕ} (f : Zero N) : Zero N := equilibrium (coefficient f)

def transverse {N : ℕ} (f : Zero N) : Zero N := f - harmonic f

theorem harmonic_closed {N : ℕ} (f : Zero N) : differential (harmonic f) = 0 := by
  funext e
  have he := leafCharge_closed e
  dsimp [differential, harmonic, equilibrium] at *
  linear_combination coefficient f * he

theorem charge_orthogonal {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    pairZero leafCharge (transverse f) = 0 := by
  rw [transverse, pair_sub_right, harmonic, pair_equilibrium]
  change pairZero leafCharge f - chargeNormSq N *
    (pairZero leafCharge f / chargeNormSq N) = 0
  field_simp [ne_of_gt (chargeNormSq_pos hN)]
  ring

theorem orthogonal {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    pairZero (harmonic f) (transverse f) = 0 := by
  rw [pairZero_symm, harmonic, pair_equilibrium, pairZero_symm,
    charge_orthogonal hN, zero_mul]

theorem reconstruction {N : ℕ} (f : Zero N) : f = harmonic f + transverse f := by
  funext s
  simp [transverse]

theorem pythagoras {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    pairZero f f = pairZero (harmonic f) (harmonic f) +
      pairZero (transverse f) (transverse f) := by
  have he : pairZero f f = pairZero (harmonic f) (harmonic f) +
      2 * pairZero (harmonic f) (transverse f) +
      pairZero (transverse f) (transverse f) := by
    calc
      _ = pairZero (harmonic f + transverse f) (harmonic f + transverse f) := by
        rw [← reconstruction]
      _ = _ := by
        simp only [pairZero, Pi.add_apply]
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
  simpa [orthogonal hN] using he

theorem differential_transverse {N : ℕ} (f : Zero N) :
    differential (transverse f) = differential f := by
  funext e
  have he := congrFun (harmonic_closed f) e
  dsimp [transverse, differential] at *
  linear_combination -he

theorem action_transverse (alpha L : ℝ) {N : ℕ} (f : Zero N) :
    action alpha L (transverse f) = action alpha L f := by
  simp only [action, form, differential_transverse]

theorem operator_transverse (alpha L : ℝ) {N : ℕ} (f : Zero N) :
    operator alpha L (transverse f) = operator alpha L f := by
  funext s
  simp only [operator, differential_transverse]

theorem harmonic_equilibrium {N : ℕ} (hN : 1 ≤ N) (q : ℝ) :
    harmonic (equilibrium (N := N) q) = equilibrium q := by
  have hc : coefficient (equilibrium (N := N) q) = q := by
    rw [coefficient, pair_equilibrium]
    change chargeNormSq N * q / chargeNormSq N = q
    field_simp [ne_of_gt (chargeNormSq_pos hN)]
  exact congrArg equilibrium hc

theorem harmonic_idempotent {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    harmonic (harmonic f) = harmonic f := harmonic_equilibrium hN _

theorem transverse_zero_iff (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    transverse f = 0 ↔ operator alpha L f = 0 := by
  constructor
  · intro hz
    rw [← operator_transverse alpha L f, hz]
    funext s
    change (∑ e, conductance alpha L e * differential (0 : Zero N) e * incidence e s) = 0
    simp [differential]
  · intro hz
    have hf := (operator_zero_iff_leaf alpha L hN f).mp hz
    have hh := harmonic_equilibrium hN (f (unit hN))
    change harmonic (equilibrium (f (unit hN))) = equilibrium (f (unit hN)) at hh
    change f - harmonic f = 0
    have hfe : f = equilibrium (f (unit hN)) := hf
    have hhf : harmonic f = f := by
      calc
        harmonic f = harmonic (equilibrium (f (unit hN))) := congrArg harmonic hfe
        _ = equilibrium (f (unit hN)) := hh
        _ = f := hfe.symm
    exact sub_eq_zero.mpr hhf.symm

theorem unique_orthogonal_coefficient {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    ∃! q : ℝ, pairZero leafCharge (f - equilibrium q) = 0 := by
  refine ⟨coefficient f, charge_orthogonal hN f, ?_⟩
  intro q hq
  rw [pair_sub_right, pair_equilibrium] at hq
  change pairZero leafCharge f - chargeNormSq N * q = 0 at hq
  unfold coefficient
  apply (eq_div_iff (ne_of_gt (chargeNormSq_pos hN))).mpr
  nlinarith [hq]

/-- The actual anchored primitive is linear; this follows from its proved
uniqueness and the actual three-leg differential. -/
def primitiveLinear {N : ℕ} (hN : 1 ≤ N) : One N →ₗ[ℝ] Zero N where
  toFun := primitive
  map_add' u v := by
    apply (unique_primitive hN (u + v)).unique
      ⟨primitive_unit hN _, differential_primitive _⟩
    constructor
    · simp [primitive_unit]
    · funext e
      change differential (fun s => primitive u s + primitive v s) e = u e + v e
      rw [differential_add]
      rw [congrFun (differential_primitive u) e, congrFun (differential_primitive v) e]
  map_smul' q u := by
    apply (unique_primitive hN (q • u)).unique
      ⟨primitive_unit hN _, differential_primitive _⟩
    constructor
    · simp [primitive_unit]
    · funext e
      have he := congrFun (differential_primitive u) e
      dsimp [differential] at he ⊢
      linear_combination q * he

def basisOne {N : ℕ} (e d : Reaction N) : ℝ := by
  classical
  exact if e = d then 1 else 0

theorem primitive_synthesis {N : ℕ} (hN : 1 ≤ N) (u : One N) :
    primitive u = ∑ e, u e • primitive (basisOne e) := by
  classical
  exact LinearMap.pi_apply_eq_sum_univ (primitiveLinear hN) u

theorem pair_primitive {N : ℕ} (hN : 1 ≤ N) (u : One N) (f : Zero N) :
    pairZero (primitive u) f = ∑ e, u e * pairZero (primitive (basisOne e)) f := by
  rw [primitive_synthesis hN u]
  simp only [pairZero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The coexact potential is computed from the actual assembly basis and
Gaussian conductance. No inverse or solvability datum is supplied. -/
def coexact (alpha L : ℝ) {N : ℕ} (f : Zero N) (e : Reaction N) : ℝ :=
  pairZero (primitive (basisOne e)) f / conductance alpha L e

theorem coexact_representation (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (f : Zero N) (hf : pairZero leafCharge f = 0) :
    adjoint alpha L (coexact alpha L f) = f := by
  have hp (g : Zero N) :
      pairZero g (adjoint alpha L (coexact alpha L f)) = pairZero g f := by
    rw [HistoryReactionComplex.adjoint_identity]
    have hsum : pairOne alpha L (differential g) (coexact alpha L f) =
        ∑ e, differential g e * pairZero (primitive (basisOne e)) f := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [coexact]
      field_simp [ne_of_gt (conductance_pos alpha L e)]
    rw [hsum, ← pair_primitive hN]
    have heq := zero_decomposition hN g
    have hz : pairZero (equilibrium (g (unit hN))) f = 0 := by
      rw [pairZero_symm, pair_equilibrium, pairZero_symm, hf, zero_mul]
    calc
      pairZero (primitive (differential g)) f =
          pairZero (equilibrium (g (unit hN)) + primitive (differential g)) f := by
        rw [pair_add_left, hz, zero_add]
      _ = pairZero g f := congrArg (fun v => pairZero v f) heq.symm
  classical
  funext s
  have hs := hp (fun t => if s = t then 1 else 0)
  simpa [pairZero] using hs

theorem complete_hodge (alpha L : ℝ) {N : ℕ} (hN : 1 ≤ N) (f : Zero N) :
    ∃! u : One N, f = harmonic f + adjoint alpha L u := by
  have hc := coexact_representation alpha L hN (transverse f) (charge_orthogonal hN f)
  refine ⟨coexact alpha L (transverse f), ?_, ?_⟩
  · change f = harmonic f + adjoint alpha L (coexact alpha L (transverse f))
    rw [hc]
    exact reconstruction f
  · intro u hu
    apply adjoint_injective alpha L N
    rw [hc]
    funext s
    have hs := congrFun hu s
    change f s = harmonic f s + adjoint alpha L u s at hs
    change adjoint alpha L u s = f s - harmonic f s
    linarith

structure Conclusions : Prop where
  exact_reconstruction : ∀ {N : ℕ} (f : Zero N), f = harmonic f + transverse f
  actual_orthogonality : ∀ {N : ℕ} (_hN : 1 ≤ N) (f : Zero N),
    pairZero (harmonic f) (transverse f) = 0
  complete_energy : ∀ {N : ℕ} (_hN : 1 ≤ N) (f : Zero N),
    pairZero f f = pairZero (harmonic f) (harmonic f) +
      pairZero (transverse f) (transverse f)
  preserved_action : ∀ (alpha L : ℝ) {N : ℕ} (f : Zero N),
    action alpha L (transverse f) = action alpha L f
  unique_reduction : ∀ {N : ℕ} (_hN : 1 ≤ N) (f : Zero N),
    ∃! q : ℝ, pairZero leafCharge (f - equilibrium q) = 0
  complete_coexact_part : ∀ (alpha L : ℝ) {N : ℕ} (_hN : 1 ≤ N) (f : Zero N),
    ∃! u : One N, f = harmonic f + adjoint alpha L u

theorem generated : Conclusions where
  exact_reconstruction := reconstruction
  actual_orthogonality := orthogonal
  complete_energy := pythagoras
  preserved_action := action_transverse
  unique_reduction := unique_orthogonal_coefficient
  complete_coexact_part := complete_hodge

end GeneratedFoundations.Analysis.HistoryReactionHodge
