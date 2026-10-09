module

public import GeneratedFoundations.Operations.SourceNumberFlow
public import GeneratedFoundations.Physical.SourceVacuumTransport
public import Mathlib.Topology.Instances.Matrix

/-!
# The continuous lift of the source number flow

The relative scalar character is the weight minus three of the specified
right-frame realization. Its action is transported by conjugation from
the original Gaussian carrier. The stabilizer is derived for arbitrary
special unitary matrices, and continuity selects one sixth root along the
real-parameter source flow.

The period proved here belongs to the lifted pair in `SU(2) × Circle`.
A period assertion for a further matter representation requires its
actual action, including a nonzero weight-one space, to be specified.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Operations.SourceNumberFlow
open GeneratedFoundations.Operations.HermiteSource (sourceCoordinates)
open GeneratedFoundations.Physical.SourceVacuumTransport

namespace GeneratedFoundations.Physical.SourcePhaseLift

abbrev RightFrame := SU2 × Circle

def rightScalarMatrix (g : SU2) (z : Circle) : Mat2 :=
  ((z : ℂ) ^ 3)⁻¹ • (g : Mat2)

def stabilizerFrame (z : Circle) : SU2 :=
  ⟨canonical ((z : ℂ) ^ 3) 0,
    canonical_mem_specialUnitary _ _ (by simp [norm_pow])⟩

theorem stabilizerFrame_matrix (z : Circle) :
    (stabilizerFrame z : Mat2) =
      Matrix.diagonal ![(z : ℂ) ^ 3, ((z : ℂ) ^ 3)⁻¹] := by
  have hc : conj (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv] using (Circle.coe_inv_eq_conj z).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stabilizerFrame, canonical, hc]

theorem continuous_stabilizerFrame : Continuous stabilizerFrame := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [canonical, Matrix.of_apply]
  all_goals fun_prop

@[simp] theorem stabilizerFrame_one : stabilizerFrame 1 = 1 := by
  apply Subtype.ext
  rw [stabilizerFrame_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rightScalarMatrix_stabilizerFrame (z : Circle) :
    rightScalarMatrix (stabilizerFrame z) z =
      Matrix.diagonal ![1, ((z ^ 6 : Circle) : ℂ)⁻¹] := by
  rw [rightScalarMatrix, stabilizerFrame_matrix]
  have hz := pow_ne_zero 3 (Circle.coe_ne_zero z)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hz, ← mul_inv_rev, ← pow_add]

def FixesVacuum (g : SU2) (z : Circle) : Prop :=
  (rightScalarMatrix g z).mulVec ![1, 0] = ![1, 0]

/-- Fixing the vector, rather than only its line, determines the whole matrix. -/
theorem fixesVacuum_iff (g : SU2) (z : Circle) :
    FixesVacuum g z ↔ g = stabilizerFrame z := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [rightScalarMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hz := pow_ne_zero 3 (Circle.coe_ne_zero z)
    have hg00 : (g : Mat2) 0 0 = (z : ℂ) ^ 3 := by
      exact ((inv_mul_eq_one₀ hz).mp h0).symm
    have hg10 : (g : Mat2) 1 0 = 0 := by
      exact h1
    have he := specialUnitary_entries (g : Mat2) g.property
    have hc := congrArg (fun M : Mat2 => M 1 0) he
    have hg01 : (g : Mat2) 0 1 = 0 := by
      have hc' := congrArg conj hc
      simpa [canonical, hg10] using hc'.symm
    apply Subtype.ext
    change (g : Mat2) = canonical ((z : ℂ) ^ 3) 0
    simpa only [hg00, hg01] using he
  · rintro rfl
    change (rightScalarMatrix (stabilizerFrame z) z).mulVec _ = _
    rw [rightScalarMatrix_stabilizerFrame]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rightScalarMatrix_injective (z : Circle) :
    Function.Injective (fun g : SU2 => rightScalarMatrix g z) := by
  intro g h he
  apply Subtype.ext
  have hz := pow_ne_zero 3 (Circle.coe_ne_zero z)
  exact smul_right_injective Mat2 (inv_ne_zero hz) he

theorem rightScalarMatrix_det (g : SU2) (z : Circle) :
    (rightScalarMatrix g z).det = ((z ^ 6 : Circle) : ℂ)⁻¹ := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  simp [rightScalarMatrix, hd, ← inv_pow, ← pow_mul]

/-- The exact kernel equations on the specified right scalar representation. -/
theorem rightScalarMatrix_eq_one_iff (g : SU2) (z : Circle) :
    rightScalarMatrix g z = 1 ↔
      (g : Mat2) = (z : ℂ) ^ 3 • (1 : Mat2) ∧ z ^ 6 = 1 := by
  constructor
  · intro h
    have hz := pow_ne_zero 3 (Circle.coe_ne_zero z)
    have hg : (g : Mat2) = (z : ℂ) ^ 3 • (1 : Mat2) := by
      exact (inv_smul_eq_iff₀ hz).mp h
    refine ⟨hg, ?_⟩
    apply Subtype.ext
    have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
    rw [hg, Matrix.det_smul] at hd
    simpa [← pow_mul] using hd
  · rintro ⟨hg, _⟩
    simp [rightScalarMatrix, hg, smul_smul, Circle.coe_ne_zero]

def phase (t : ℝ) : Circle := Circle.exp (t / 6)

theorem continuous_phase : Continuous phase :=
  Circle.exp.continuous.comp (continuous_id.div_const 6)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_sixth_power (t : ℝ) : phase t ^ 6 = Circle.exp t := by
  rw [phase, ← Circle.exp_natCast_mul]
  congr 1
  ring

theorem phase_cube (t : ℝ) :
    (phase t : ℂ) ^ 3 = Complex.exp (Complex.I * (t : ℂ) / 2) := by
  have h : phase t ^ 3 = Circle.exp (t / 2) := by
    rw [phase, ← Circle.exp_natCast_mul]
    congr 1
    ring
  rw [← Circle.coe_pow, h, Circle.coe_exp]
  congr 1
  push_cast
  ring

def lift (t : ℝ) : RightFrame := (stabilizerFrame (phase t), phase t)

theorem continuous_lift : Continuous lift :=
  (continuous_stabilizerFrame.comp continuous_phase).prodMk continuous_phase

@[simp] theorem lift_zero : lift 0 = 1 := by simp [lift]

theorem lift_spinMatrix (t : ℝ) : ((lift t).1 : Mat2) = zRotation (-t) := by
  change canonical ((phase t : ℂ) ^ 3) 0 = _
  rw [phase_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonical, zRotation, ← Complex.exp_conj, map_ofNat]

theorem lift_spec (t : ℝ) :
    rightScalarMatrix (lift t).1 (lift t).2 = numberFlowMatrix t := by
  change rightScalarMatrix (stabilizerFrame (phase t)) (phase t) = _
  rw [rightScalarMatrix_stabilizerFrame, phase_sixth_power]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFlowMatrix, Circle.coe_exp, ← Complex.exp_neg]
  congr 1
  ring

theorem phase_forced (g : SU2) (z : Circle) (t : ℝ)
    (h : rightScalarMatrix g z = numberFlowMatrix t) : z ^ 6 = Circle.exp t := by
  have hd := congrArg Matrix.det h
  rw [rightScalarMatrix_det, numberFlowMatrix_det, number_phase_eq_circle] at hd
  simp only [Circle.exp_neg, Circle.coe_inv] at hd
  exact Subtype.ext (inv_injective hd)

/-- Continuity removes the six pointwise choices of a sixth root. No group
law for a competing lift is assumed. -/
theorem continuous_lift_unique (f : ℝ → RightFrame) (hf : Continuous f)
    (hzero : f 0 = 1)
    (hflow : ∀ t, rightScalarMatrix (f t).1 (f t).2 = numberFlowMatrix t) :
    f = lift := by
  have hphase : (fun t => (f t).2) = phase := by
    refine (Circle.isQuotientCoveringMap_npow 6).isCoveringMap.eq_of_comp_eq
      (continuous_snd.comp hf) continuous_phase ?_ (0 : ℝ) ?_
    · funext t
      exact (phase_forced _ _ _ (hflow t)).trans (phase_sixth_power t).symm
    · simpa using congrArg Prod.snd hzero
  funext t
  apply Prod.ext
  · apply rightScalarMatrix_injective (phase t)
    have h := hflow t
    rw [congrFun hphase t] at h
    exact h.trans (lift_spec t).symm
  · exact congrFun hphase t

theorem phase_surjective : Function.Surjective phase := by
  intro z
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  refine ⟨6 * t, ?_⟩
  simpa [phase] using ht

theorem mem_lift_range_iff (g : SU2) (z : Circle) :
    (g, z) ∈ Set.range lift ↔ FixesVacuum g z := by
  rw [fixesVacuum_iff]
  constructor
  · rintro ⟨t, ht⟩
    have hg := congrArg Prod.fst ht
    have hz := congrArg Prod.snd ht
    exact hg.symm.trans (congrArg stabilizerFrame hz)
  · rintro rfl
    obtain ⟨t, rfl⟩ := phase_surjective z
    exact ⟨t, rfl⟩

theorem lift_eq_one_iff (t : ℝ) :
    lift t = 1 ↔ ∃ k : ℤ, t = k * (12 * Real.pi) := by
  have h : lift t = 1 ↔ phase t = 1 := by
    constructor
    · exact fun he => congrArg Prod.snd he
    · intro he
      simp [lift, he]
  rw [h, phase, Circle.exp_eq_one]
  constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩ <;> linarith

theorem lift_periodic_iff (t : ℝ) :
    Function.Periodic lift t ↔ ∃ k : ℤ, t = k * (12 * Real.pi) := by
  constructor
  · intro h
    apply (lift_eq_one_iff t).mp
    simpa using h 0
  · rintro ⟨k, rfl⟩ s
    have hp : phase (s + k * (12 * Real.pi)) = phase s := by
      unfold phase
      rw [show (s + k * (12 * Real.pi)) / 6 = s / 6 + k * (2 * Real.pi) by ring,
        Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    simp only [lift, hp]

theorem lift_least_positive_period :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic lift t} (12 * Real.pi) := by
  have hp : 0 < 12 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨⟨hp, (lift_periodic_iff _).mpr ⟨1, by simp⟩⟩, ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := (lift_periodic_iff t).mp ht.2
  have hkpos : (0 : ℝ) < k := (mul_pos_iff_of_pos_right hp).mp (by
    rw [← hk]
    exact ht.1)
  have hkpos_int : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hkone_int : (1 : ℤ) ≤ k := by omega
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkone_int
  calc
    12 * Real.pi = 1 * (12 * Real.pi) := (one_mul _).symm
    _ ≤ (k : ℝ) * (12 * Real.pi) := mul_le_mul_of_nonneg_right hkone hp.le
    _ = t := hk.symm

variable {b : ℝ} (hb : 0 < b)

def rightAction (g : SU2) (z : Circle) : Module.End ℂ (TwistedCarrier hb) :=
  conjugatedAction hb (rightScalarMatrix g z)

/-- The coordinate stabilizer is the pointwise stabilizer of the transported
Gaussian vacuum, not merely a stabilizer of a chosen abstract doublet. -/
theorem rightAction_fixesVacuum_iff (g : SU2) (z : Circle) :
    rightAction hb g z (transportedVacuum hb) = transportedVacuum hb ↔
      FixesVacuum g z := by
  have h0 : sourceCoordinates hb (basisVector hb 0) =
      WithLp.toLp 2 ![(1 : ℂ), 0] := by
    ext i
    fin_cases i <;> simp
  change conjugatedAction hb (rightScalarMatrix g z)
    (transport hb (basisVector hb 0)) = transport hb (basisVector hb 0) ↔ _
  rw [conjugatedAction_transport, (transport hb).injective.eq_iff,
    ← (sourceCoordinates hb).injective.eq_iff, sourceAction_coordinates, h0]
  exact (WithLp.toLp_injective 2).eq_iff

theorem mem_lift_range_iff_fixes_source_vacuum (g : SU2) (z : Circle) :
    (g, z) ∈ Set.range lift ↔
      rightAction hb g z (transportedVacuum hb) = transportedVacuum hb := by
  rw [mem_lift_range_iff, rightAction_fixesVacuum_iff]

/-- The lifted action on the actual transported source is the original
number flow, with no determinant multiplier. -/
theorem rightAction_lift_source (t : ℝ) (v : V hb) :
    (((transport hb).symm
      (rightAction hb (lift t).1 (lift t).2 (transport hb v))) :
        GeneratedFoundations.Correlation.ComplexGaussianStates.ComplexL2) =
      numberFlow hb t v := by
  rw [rightAction, lift_spec, conjugatedAction_transport,
    LinearIsometryEquiv.symm_apply_apply, sourceAction_control, numberFlow_control]

theorem rightAction_lift_vacuum (t : ℝ) :
    rightAction hb (lift t).1 (lift t).2 (transportedVacuum hb) =
      transportedVacuum hb := by
  change conjugatedAction hb (rightScalarMatrix (lift t).1 (lift t).2)
    (transport hb (basisVector hb 0)) = transport hb (basisVector hb 0)
  rw [lift_spec, conjugatedAction_transport]
  congr 1
  rw [sourceAction_basis]
  simp [numberFlowMatrix]

end GeneratedFoundations.Physical.SourcePhaseLift
