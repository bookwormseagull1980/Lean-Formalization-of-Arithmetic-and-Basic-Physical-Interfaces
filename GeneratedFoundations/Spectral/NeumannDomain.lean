module

public import GeneratedFoundations.Spectral.IntervalSobolev
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# The Neumann domain and its differential operator

The operator acts on actual interval `L²` classes represented by second-order
Sobolev functions. Its value is the negative second derivative. Representative
independence, Green's identity, and the constant kernel are established before
any eigenfunction expansion is introduced.

This is an internally defined operator, not a field of the root change datum.
`ReflectionSobolev` identifies its domain through even reflection, and the
downstream Gaussian-average theorem identifies the actual source evolution.
The separated-boundary theorem below classifies competing constant-preserving
boundary conditions; its comparison assumptions are not extra root inputs.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

lemma integral_congr_intervalMeasure {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (heq : f =ᵐ[intervalMeasure a b] g) :
    (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp heq] with x hx hxi
  apply hx
  simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hxi

theorem h1_integrationByParts {a b : ℝ} (hab : a ≤ b)
    {f g f' g' : ℝ → ℝ} (hf : HasH1Derivative a b f f')
    (hg : HasH1Derivative a b g g') :
    (∫ x in a..b, f x * g' x) =
      f b * g b - f a * g a - ∫ x in a..b, f' x * g x := by
  calc
    (∫ x in a..b, f x * g' x) = ∫ x in a..b, f x * deriv g x := by
      apply integral_congr_intervalMeasure hab
      filter_upwards [hg.deriv_eq_ae] with x hx
      rw [hx]
    _ = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x :=
      hf.absolutelyContinuous.integral_mul_deriv_eq_deriv_mul hg.absolutelyContinuous
    _ = f b * g b - f a * g a - ∫ x in a..b, f' x * g x := by
      congr 1
      apply integral_congr_intervalMeasure hab
      filter_upwards [hf.deriv_eq_ae] with x hx
      rw [hx]

/-- The Sobolev derivative satisfies the weak integration identity against
all zero-boundary `H¹` test functions. -/
theorem h1_weakDerivative {a b : ℝ} (hab : a ≤ b)
    {f f' ψ ψ' : ℝ → ℝ} (hf : HasH1Derivative a b f f')
    (hψ : HasH1Derivative a b ψ ψ') (hleft : ψ a = 0) (hright : ψ b = 0) :
    (∫ x in a..b, f x * ψ' x) = -(∫ x in a..b, f' x * ψ x) := by
  rw [h1_integrationByParts hab hf hψ, hleft, hright]
  simp

/-- Both endpoint traces of the first derivative vanish. -/
def IsNeumann {a b : ℝ} (f : H2Representative a b) : Prop :=
  f.first a = 0 ∧ f.first b = 0

theorem neumann_greenIdentity {a b : ℝ} (hab : a ≤ b)
    (f g : H2Representative a b) (hf : IsNeumann f) :
    (∫ x in a..b, (-f.second x) * g.value x) =
      ∫ x in a..b, f.first x * g.first x := by
  have hparts := h1_integrationByParts hab g.firstDerivative f.secondDerivative
  have hswap : (∫ x in a..b, g.first x * f.first x) =
      ∫ x in a..b, f.first x * g.first x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  calc
    (∫ x in a..b, (-f.second x) * g.value x) =
        -(∫ x in a..b, g.value x * f.second x) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = ∫ x in a..b, f.first x * g.first x := by
      rw [hparts, hf.1, hf.2, hswap]
      simp

theorem neumann_nonnegative {a b : ℝ} (hab : a ≤ b)
    (f : H2Representative a b) (hf : IsNeumann f) :
    0 ≤ ∫ x in a..b, (-f.second x) * f.value x := by
  rw [neumann_greenIdentity hab f f hf]
  exact intervalIntegral.integral_nonneg_of_forall hab fun x => mul_self_nonneg _

theorem neumann_symmetric {a b : ℝ} (hab : a ≤ b)
    (f g : H2Representative a b) (hf : IsNeumann f) (hg : IsNeumann g) :
    (∫ x in a..b, (-f.second x) * g.value x) =
      ∫ x in a..b, f.value x * (-g.second x) := by
  rw [neumann_greenIdentity hab f g hf]
  have h := neumann_greenIdentity hab g f hg
  simpa only [mul_comm] using h.symm

theorem neumann_kernel_constants {a b : ℝ} (hab : a < b)
    (f : H2Representative a b) (hf : IsNeumann f) :
    f.secondL2 = 0 ↔ ∃ c : ℝ, ∀ x ∈ Icc a b, f.value x = c := by
  constructor
  · intro hz
    have hs : f.second =ᵐ[intervalMeasure a b] 0 := by
      have h := f.secondDerivative.derivative_memLp.coeFn_toLp
      change f.secondL2 =ᵐ[intervalMeasure a b] f.second at h
      rw [hz] at h
      exact h.symm.trans (Lp.coeFn_zero ℝ 2 (intervalMeasure a b))
    have hfirst : ∀ x ∈ Icc a b, f.first x = 0 := by
      intro x hx
      rw [f.secondDerivative.constant_of_derivative_eq_zero hab.le hs x hx, hf.1]
    have hfirst_ae : f.first =ᵐ[intervalMeasure a b] 0 :=
      ae_restrict_of_forall_mem measurableSet_Icc hfirst
    exact ⟨f.value a, f.firstDerivative.constant_of_derivative_eq_zero hab.le hfirst_ae⟩
  · rintro ⟨c, hc⟩
    have heq : f.toL2 = (H2Representative.constant a b c).toL2 := by
      apply (f.toL2_eq_iff _).mpr
      exact ae_restrict_of_forall_mem measurableSet_Icc hc
    have hsecond := H2Representative.secondL2_unique hab heq
    exact hsecond

/-- A nonzero separated real homogeneous boundary condition. -/
structure SeparatedBoundary where
  valueCoefficient : ℝ
  derivativeCoefficient : ℝ
  nontrivial : valueCoefficient ≠ 0 ∨ derivativeCoefficient ≠ 0

def SeparatedBoundary.accepts (B : SeparatedBoundary) (value derivative : ℝ) : Prop :=
  B.valueCoefficient * value + B.derivativeCoefficient * derivative = 0

theorem SeparatedBoundary.constant_preserving_iff (B : SeparatedBoundary)
    (hconstant : B.accepts 1 0) (value derivative : ℝ) :
    B.accepts value derivative ↔ derivative = 0 := by
  have hvalue : B.valueCoefficient = 0 := by simpa [accepts] using hconstant
  have hderivative : B.derivativeCoefficient ≠ 0 := B.nontrivial.resolve_left (by simp [hvalue])
  simp [accepts, hvalue, hderivative]

/-- Conservation of the constant state selects the Neumann member of the
separated homogeneous boundary class at both endpoints. -/
theorem separatedClosure_selects_neumann {a b : ℝ} (L R : SeparatedBoundary)
    (hL : L.accepts 1 0) (hR : R.accepts 1 0) (f : H2Representative a b) :
    (L.accepts (f.value a) (f.first a) ∧ R.accepts (f.value b) (f.first b)) ↔ IsNeumann f := by
  rw [L.constant_preserving_iff hL, R.constant_preserving_iff hR]
  rfl

/-- The domain is a subspace of the actual interval `L²` space. -/
noncomputable def neumannDomain (a b : ℝ) : Submodule ℝ (IntervalL2 a b) where
  carrier := {u | ∃ f : H2Representative a b, IsNeumann f ∧ f.toL2 = u}
  zero_mem' := ⟨H2Representative.constant a b 0, ⟨rfl, rfl⟩, rfl⟩
  add_mem' := by
    rintro u v ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f.add g, by simp [IsNeumann, H2Representative.add, hf.1, hf.2, hg.1, hg.2],
      H2Representative.toL2_add f g⟩
  smul_mem' := by
    rintro c u ⟨f, hf, rfl⟩
    exact ⟨f.smul c, by simp [IsNeumann, H2Representative.smul, hf.1, hf.2],
      H2Representative.toL2_smul c f⟩

noncomputable def neumannRepresentative {a b : ℝ} (u : neumannDomain a b) :
    H2Representative a b := Classical.choose u.property

theorem neumannRepresentative_spec {a b : ℝ} (u : neumannDomain a b) :
    IsNeumann (neumannRepresentative u) ∧ (neumannRepresentative u).toL2 = (u : IntervalL2 a b) :=
  Classical.choose_spec u.property

/-- The unbounded differential operator, with its genuine Sobolev domain. -/
noncomputable def neumannOperator {a b : ℝ} (hab : a < b) :
    IntervalL2 a b →ₗ.[ℝ] IntervalL2 a b where
  domain := neumannDomain a b
  toFun :=
    { toFun := fun u => -(neumannRepresentative u).secondL2
      map_add' := by
        intro u v
        have heq : (neumannRepresentative (u + v)).toL2 =
            ((neumannRepresentative u).add (neumannRepresentative v)).toL2 := by
          rw [H2Representative.toL2_add, (neumannRepresentative_spec (u + v)).2,
            (neumannRepresentative_spec u).2, (neumannRepresentative_spec v).2]
          rfl
        rw [H2Representative.secondL2_unique hab heq, H2Representative.secondL2_add, neg_add]
      map_smul' := by
        intro c u
        have heq : (neumannRepresentative (c • u)).toL2 =
            ((neumannRepresentative u).smul c).toL2 := by
          rw [H2Representative.toL2_smul, (neumannRepresentative_spec (c • u)).2,
            (neumannRepresentative_spec u).2]
          rfl
        rw [H2Representative.secondL2_unique hab heq, H2Representative.secondL2_smul,
          smul_neg]
        rfl }

theorem neumannOperator_on_representative {a b : ℝ} (hab : a < b)
    (f : H2Representative a b) (hf : IsNeumann f) :
    (neumannOperator hab).toFun ⟨f.toL2, f, hf, rfl⟩ = -f.secondL2 := by
  change -(neumannRepresentative ⟨f.toL2, f, hf, rfl⟩).secondL2 = -f.secondL2
  congr 1
  exact H2Representative.secondL2_unique hab (neumannRepresentative_spec _).2

end GeneratedFoundations.Spectral
