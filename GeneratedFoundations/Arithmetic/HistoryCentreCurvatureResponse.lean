module

public import GeneratedFoundations.Arithmetic.HistoryCentrePotential
public import GeneratedFoundations.Arithmetic.HistoryCurvatureVariation
public import GeneratedFoundations.Geometry.HilbertPolynomialVariation

/-!
# Centre-weighted curvature of the complete arithmetic carrier

The weight acts on every column of the actual history--phase/source
operator. It is the exponential of the already constructed source grading.
At the unbiased source it is one, so the complete trace action is recovered.
No scalar replacement of the operator or deletion of mixed matrix entries
is used. The source derivative and the connection derivative are taken in
the same nonlinear functional. Their mixed term is retained at a general
background and vanishes at a flat background by the curvature equation.

The displacement and the connection are configuration variables. The
unbiased source, its centre character and its restoring potential were
constructed before these variables were introduced.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCentreCurvatureResponse

open HistoryCliffordAction (Index Space)
open HistoryGaugeJets
open Geometry.HilbertPolynomialVariation

def centreSign {N : ℕ} (i : Index N) : ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1) i.2

def basis (N : ℕ) : OrthonormalBasis (Index N) ℂ (Space N) :=
  EuclideanSpace.basisFun (Index N) ℂ

def weight {N : ℕ} (h : ℝ) (i : Index N) : ℝ := Real.exp (h * centreSign i)

theorem weight_positive {N : ℕ} (h : ℝ) (i : Index N) : 0 < weight h i :=
  Real.exp_pos _

@[simp] theorem weight_zero {N : ℕ} (i : Index N) : weight 0 i = 1 := by
  simp [weight]

theorem weight_hasDerivAt {N : ℕ} (h : ℝ) (i : Index N) :
    HasDerivAt (fun u => weight u i) (weight h i * centreSign i) h := by
  simpa [weight] using ((hasDerivAt_id h).mul_const (centreSign i)).exp

/-- The column weights have precisely the already generated centre
partition, including every actual history and phase multiplicity. -/
theorem complete_partition (N : ℕ) (h : ℝ) :
    (∑ i : Index N, weight h i) / Fintype.card (Index N) =
      HistoryJointCentreResponse.partition N h := by
  have hc : (Fintype.card (HistoryCliffordAction.HistoryLabel N) : ℝ) ≠ 0 := by
    have hn : Nonempty (HistoryCliffordAction.HistoryLabel N) :=
      ⟨HistoryCliffordAction.historyPoint N⟩
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (HistoryCliffordAction.HistoryLabel N) ≠ 0)
  rw [HistoryJointCentreResponse.partition_eq_cosh]
  simp [Index, weight, centreSign, Operations.SourceCliffordConnector.ChiralIndex,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Real.cosh_eq]
  field_simp
  ring

def weightedEnergy (N : ℕ) (h : ℝ) (X : Operator N) : ℝ :=
  ∑ i, weight h i * energy (X (basis N i))

def sourceEnergy (N : ℕ) (h : ℝ) (X : Operator N) : ℝ :=
  ∑ i, weight h i * centreSign i * energy (X (basis N i))

def weightedPair (N : ℕ) (h : ℝ) (X Y : Operator N) : ℝ :=
  ∑ i, weight h i * inner ℝ (X (basis N i)) (Y (basis N i))

def sourcePair (N : ℕ) (h : ℝ) (X Y : Operator N) : ℝ :=
  ∑ i, weight h i * centreSign i * inner ℝ (X (basis N i)) (Y (basis N i))

theorem weightedEnergy_nonneg (N : ℕ) (h : ℝ) (X : Operator N) :
    0 ≤ weightedEnergy N h X :=
  Finset.sum_nonneg fun i _ => mul_nonneg (weight_positive h i).le
    (div_nonneg (sq_nonneg _) (by norm_num))

theorem weightedEnergy_unbiased (N : ℕ) (X : Operator N) :
    weightedEnergy N 0 X = Geometry.HilbertTraceQuadratic.energy X / 2 := by
  rw [Geometry.HilbertTraceQuadratic.energy_basis (basis N)]
  simp [weightedEnergy, energy, Finset.sum_div]

theorem weightedEnergy_source_derivative (N : ℕ) (h : ℝ) (X : Operator N) :
    HasDerivAt (fun u => weightedEnergy N u X) (sourceEnergy N h X) h := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (weight_hasDerivAt h i).mul_const (energy (X (basis N i)))) using 1
  funext u
  simp only [weightedEnergy, Finset.sum_apply]

theorem weightedPair_source_derivative (N : ℕ) (h : ℝ) (X Y : Operator N) :
    HasDerivAt (fun u => weightedPair N u X Y) (sourcePair N h X Y) h := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (weight_hasDerivAt h i).mul_const (inner ℝ (X (basis N i)) (Y (basis N i)))) using 1
  funext u
  simp only [weightedPair, Finset.sum_apply]

/-- The original source potential and the complete nonlinear curvature
are observed with the same source-centre exponential. -/
def action (N : ℕ) (h : ℝ) (A : ConnectionJet N) : ℝ :=
  HistoryCentrePotential.potential N h +
    ∑ μ, ∑ ν, weightedEnergy N h (curvature A μ ν)

theorem action_nonneg (N : ℕ) (h : ℝ) (A : ConnectionJet N) :
    0 ≤ action N h A := add_nonneg (HistoryCentrePotential.potential_nonneg N h)
  (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    weightedEnergy_nonneg N h _)

theorem action_unbiased (N : ℕ) (A : ConnectionJet N) :
    action N 0 A = HistoryCurvatureVariation.action N A := by
  simp only [action, HistoryCentrePotential.potential_zero, zero_add,
    weightedEnergy_unbiased, HistoryCurvatureVariation.action,
    curvatureDensity, quadratic, Finset.sum_div]

theorem action_flat (N : ℕ) (h : ℝ) (A : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) :
    action N h A = HistoryCentrePotential.potential N h := by
  simp [action, hA, weightedEnergy, energy]

def sourceForce (N : ℕ) (h : ℝ) (A : ConnectionJet N) : ℝ :=
  HistoryCentrePotential.force N h + ∑ μ, ∑ ν, sourceEnergy N h (curvature A μ ν)

theorem action_source_derivative (N : ℕ) (h : ℝ) (A : ConnectionJet N) :
    HasDerivAt (fun u => action N u A) (sourceForce N h A) h := by
  convert! (HistoryCentrePotential.potential_hasDerivAt N h).add
    (HasDerivAt.sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) fun ν _ =>
        weightedEnergy_source_derivative N h (curvature A μ ν)) using 1
  funext u
  simp only [action, Pi.add_apply, Finset.sum_apply]

def firstVariation (N : ℕ) (h : ℝ) (A V : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, weightedPair N h (curvature A μ ν)
    (HistoryCurvatureVariation.linearized N A V μ ν)

theorem action_connection_derivative (N : ℕ) (h : ℝ) (A V : ConnectionJet N) :
    HasDerivAt (fun t : ℝ => action N h
      (HistoryCurvatureVariation.line N A V (t : ℂ))) (firstVariation N h A V) 0 := by
  have hc (μ ν : CoordinateIndex N) (i : Index N) :
      (fun t : ℝ => energy
        (curvature (HistoryCurvatureVariation.line N A V (t : ℂ)) μ ν (basis N i))) =
      (fun t : ℝ => energy (curvature A μ ν (basis N i) +
        t • HistoryCurvatureVariation.linearized N A V μ ν (basis N i) +
        t ^ 2 • HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i))) := by
    funext t
    rw [HistoryCurvatureVariation.curvature_line]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, ← Complex.ofReal_pow, Complex.coe_smul]
  have hcp (t : ℝ) (μ ν : CoordinateIndex N) (i : Index N) := congrFun (hc μ ν i) t
  have hd (μ ν : CoordinateIndex N) (i : Index N) :=
    (energy_quadratic_path_hasDerivAt (curvature A μ ν (basis N i))
      (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
      (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i)) 0).const_mul (weight h i)
  have hs := (hasDerivAt_const (0 : ℝ) (HistoryCentrePotential.potential N h)).add
    (HasDerivAt.sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) fun ν _ =>
        HasDerivAt.sum (u := Finset.univ) fun i _ => hd μ ν i)
  convert! hs using 1
  · funext t
    simp only [action, weightedEnergy, hcp, Finset.sum_apply, Pi.add_apply]
  · simp [firstVariation, weightedPair]

def mixedVariation (N : ℕ) (h : ℝ) (A V : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, sourcePair N h (curvature A μ ν)
    (HistoryCurvatureVariation.linearized N A V μ ν)

theorem firstVariation_source_derivative (N : ℕ) (h : ℝ) (A V : ConnectionJet N) :
    HasDerivAt (fun u => firstVariation N u A V) (mixedVariation N h A V) h := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) (fun ν _ =>
        weightedPair_source_derivative N h (curvature A μ ν)
          (HistoryCurvatureVariation.linearized N A V μ ν))) using 1
  funext u
  simp only [firstVariation, Finset.sum_apply]

/-- This is the actual iterated derivative of the one common action. -/
theorem action_mixed_derivative (N : ℕ) (h : ℝ) (A V : ConnectionJet N) :
    deriv (fun u => deriv (fun t : ℝ => action N u
      (HistoryCurvatureVariation.line N A V (t : ℂ))) 0) h =
      mixedVariation N h A V := by
  have he : (fun u => deriv (fun t : ℝ => action N u
      (HistoryCurvatureVariation.line N A V (t : ℂ))) 0) =
      fun u => firstVariation N u A V :=
    funext fun u => (action_connection_derivative N u A V).deriv
  rw [he]
  exact (firstVariation_source_derivative N h A V).deriv

theorem mixedVariation_flat_zero (N : ℕ) (h : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) : mixedVariation N h A V = 0 := by
  simp [mixedVariation, sourcePair, hA]

theorem weightedPair_symm (N : ℕ) (h : ℝ) (X Y : Operator N) :
    weightedPair N h X Y = weightedPair N h Y X := by
  simp only [weightedPair, real_inner_comm]

theorem weightedPair_self_nonneg (N : ℕ) (h : ℝ) (X : Operator N) :
    0 ≤ weightedPair N h X X := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (weight_positive h i).le (real_inner_self_nonneg)

/-- Both field slots are varied in the same source-weighted action. The
background pairing with the commutator variation is part of the Hessian. -/
def hessian (N : ℕ) (h : ℝ) (A V W : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, (weightedPair N h
    (HistoryCurvatureVariation.linearized N A W μ ν)
    (HistoryCurvatureVariation.linearized N A V μ ν) +
    weightedPair N h (curvature A μ ν)
      (HistoryCurvatureVariation.mixedCurvature N V W μ ν))

theorem hessian_symm (N : ℕ) (h : ℝ) (A V W : ConnectionJet N) :
    hessian N h A V W = hessian N h A W V := by
  unfold hessian
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  rw [weightedPair_symm N h,
    HistoryCurvatureVariation.mixedCurvature_symm N V W]

/-- At the unbiased source this is exactly the original full trace Hessian,
including the background-curvature pairing with the mixed commutator. -/
theorem hessian_unbiased (N : ℕ) (A V W : ConnectionJet N) :
    hessian N 0 A V W = HistoryCurvatureVariation.hessian N A V W := by
  have hp (X Y : Operator N) :
      weightedPair N 0 X Y = Geometry.HilbertTraceVariation.pair X Y := by
    rw [Geometry.HilbertTraceVariation.pair_basis (basis N)]
    simp only [weightedPair, weight_zero, one_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
      (X (basis N i)) (Y (basis N i))).trans
        (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
          (𝕜 := ℂ) (X (basis N i)) (Y (basis N i))).symm
  simp only [hessian, HistoryCurvatureVariation.hessian, hp]

theorem firstVariation_connection_derivative (N : ℕ) (h : ℝ)
    (A V W : ConnectionJet N) :
    HasDerivAt (fun t : ℝ => firstVariation N h
      (HistoryCurvatureVariation.line N A W (t : ℂ)) V)
      (hessian N h A V W) 0 := by
  have hd (μ ν : CoordinateIndex N) (i : Index N) :=
    (inner_quadratic_linear_hasDerivAt_zero
      (curvature A μ ν (basis N i))
      (HistoryCurvatureVariation.linearized N A W μ ν (basis N i))
      (HistoryCurvatureVariation.quadraticTerm N W μ ν (basis N i))
      (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
      (HistoryCurvatureVariation.mixedCurvature N V W μ ν (basis N i))).const_mul
        (weight h i)
  have hs := HasDerivAt.sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) fun ν _ =>
      HasDerivAt.sum (u := Finset.univ) fun i _ => hd μ ν i
  convert! hs using 1
  · funext t
    simp only [firstVariation, weightedPair, HistoryCurvatureVariation.curvature_line,
      HistoryCurvatureVariation.linearized_line, LinearMap.add_apply,
      LinearMap.smul_apply, ← Complex.ofReal_pow, Complex.coe_smul,
      Finset.sum_apply]
  · simp only [hessian, weightedPair, Finset.sum_add_distrib, mul_add]

theorem action_field_hessian (N : ℕ) (h : ℝ) (A V W : ConnectionJet N) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N h
      (HistoryCurvatureVariation.line N
        (HistoryCurvatureVariation.line N A W (t : ℂ)) V (s : ℂ))) 0) 0 =
      hessian N h A V W := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => action N h
      (HistoryCurvatureVariation.line N
        (HistoryCurvatureVariation.line N A W (t : ℂ)) V (s : ℂ))) 0) =
      fun t : ℝ => firstVariation N h (HistoryCurvatureVariation.line N A W (t : ℂ)) V :=
    funext fun t => (action_connection_derivative N h _ V).deriv
  rw [he]
  exact (firstVariation_connection_derivative N h A V W).deriv

theorem hessian_flat_nonneg (N : ℕ) (h : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) : 0 ≤ hessian N h A V V := by
  simp only [hessian, hA, weightedPair, LinearMap.zero_apply, inner_zero_left,
    mul_zero, Finset.sum_const_zero, add_zero]
  exact Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ =>
    weightedPair_self_nonneg N h (HistoryCurvatureVariation.linearized N A V μ ν)

@[simp] theorem centreSign_sq {N : ℕ} (i : Index N) : centreSign i ^ 2 = 1 := by
  rcases i with ⟨a, b | b⟩ <;> norm_num [centreSign]

theorem sourceEnergy_source_derivative (N : ℕ) (h : ℝ) (X : Operator N) :
    HasDerivAt (fun u => sourceEnergy N u X) (weightedEnergy N h X) h := by
  have hs := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    ((weight_hasDerivAt h i).mul_const (centreSign i)).mul_const (energy (X (basis N i)))
  convert! hs using 1
  · funext u
    simp only [sourceEnergy, Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc (weight h i) (centreSign i) (centreSign i), ← pow_two, centreSign_sq]
    simp

def sourceHessian (N : ℕ) (h : ℝ) (A : ConnectionJet N) : ℝ :=
  HistoryJointCentreResponse.susceptibility N h +
    ∑ μ, ∑ ν, weightedEnergy N h (curvature A μ ν)

theorem sourceForce_derivative (N : ℕ) (h : ℝ) (A : ConnectionJet N) :
    HasDerivAt (fun u => sourceForce N u A) (sourceHessian N h A) h := by
  convert! (HistoryCentrePotential.force_hasDerivAt N h).add
    (HasDerivAt.sum (u := Finset.univ) fun μ _ =>
      HasDerivAt.sum (u := Finset.univ) fun ν _ =>
        sourceEnergy_source_derivative N h (curvature A μ ν)) using 1
  funext u
  simp only [sourceForce, Pi.add_apply, Finset.sum_apply]

theorem action_source_hessian (N : ℕ) (h : ℝ) (A : ConnectionJet N) :
    deriv (fun u => deriv (fun v => action N v A) u) h = sourceHessian N h A := by
  have he : (fun u => deriv (fun v => action N v A) u) =
      fun u => sourceForce N u A := funext fun u => (action_source_derivative N u A).deriv
  rw [he]
  exact (sourceForce_derivative N h A).deriv

theorem sourceHessian_positive (N : ℕ) (h : ℝ) (A : ConnectionJet N) :
    0 < sourceHessian N h A :=
  add_pos_of_pos_of_nonneg (HistoryJointCentreResponse.susceptibility_pos N h)
    (Finset.sum_nonneg fun _μ _ => Finset.sum_nonneg fun _ν _ =>
      weightedEnergy_nonneg N h _)

theorem sourceHessian_unbiased_flat (N : ℕ) (A : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) : sourceHessian N 0 A = 1 := by
  simp [sourceHessian, hA, weightedEnergy, energy,
    HistoryJointCentreResponse.closed_susceptibility]

structure Conclusions : Prop where
  same_complete_source : ∀ N h,
    (∑ i : Index N, weight h i) / Fintype.card (Index N) =
      HistoryJointCentreResponse.partition N h
  actual_positive_action : ∀ N h A, 0 ≤ action N h A
  original_trace_recovered : ∀ N A, action N 0 A = HistoryCurvatureVariation.action N A
  actual_source_force : ∀ N h A,
    HasDerivAt (fun u => action N u A) (sourceForce N h A) h
  actual_connection_force : ∀ N h A V,
    HasDerivAt (fun t : ℝ => action N h
      (HistoryCurvatureVariation.line N A V (t : ℂ))) (firstVariation N h A V) 0
  retained_mixed_derivative : ∀ N h A V,
    deriv (fun u => deriv (fun t : ℝ => action N u
      (HistoryCurvatureVariation.line N A V (t : ℂ))) 0) h = mixedVariation N h A V
  flat_mixed_zero : ∀ N h A V, (∀ μ ν, curvature A μ ν = 0) →
    mixedVariation N h A V = 0
  actual_field_hessian : ∀ N h A V W,
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N h
      (HistoryCurvatureVariation.line N
        (HistoryCurvatureVariation.line N A W (t : ℂ)) V (s : ℂ))) 0) 0 =
      hessian N h A V W
  symmetric_field_hessian : ∀ N h A V W, hessian N h A V W = hessian N h A W V
  actual_source_hessian : ∀ N h A,
    deriv (fun u => deriv (fun v => action N v A) u) h = sourceHessian N h A
  positive_source_hessian : ∀ N h A, 0 < sourceHessian N h A

theorem generated : Conclusions where
  same_complete_source := complete_partition
  actual_positive_action := action_nonneg
  original_trace_recovered := action_unbiased
  actual_source_force := action_source_derivative
  actual_connection_force := action_connection_derivative
  retained_mixed_derivative := action_mixed_derivative
  flat_mixed_zero := mixedVariation_flat_zero
  actual_field_hessian := action_field_hessian
  symmetric_field_hessian := hessian_symm
  actual_source_hessian := action_source_hessian
  positive_source_hessian := sourceHessian_positive

end GeneratedFoundations.Arithmetic.HistoryCentreCurvatureResponse
