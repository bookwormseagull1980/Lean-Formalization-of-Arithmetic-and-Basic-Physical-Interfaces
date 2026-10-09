module

public import GeneratedFoundations.Geometry.SourceAxisDifferentiation
public import GeneratedFoundations.Geometry.SourceSchurOrthogonality
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Data.Finsupp.Basic

/-!
# Actual source derivatives of matrix coefficients

Each axis derivative is defined by differentiating the original group
function along right multiplication by a source-axis curve. The actual
Hilbert orbit derivatives identify its action on matrix coefficients.
Iteration gives the second derivatives, and the polynomial Casimir identity
then gives the eigenvalue on these functions. No differential eigenvalue is
included in a definition or assumed as an input.

The finite-sum statements allow arbitrary degrees and arbitrary vectors in
their actual Haar Hilbert carriers. They are pointwise identities, suitable
for transport to the same source Haar `L²` space in a separate closure proof.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourceSchurOrthogonality

namespace GeneratedFoundations.Geometry.SourceCoefficientDifferentiation

/-- The three actual source curves, all with their original half-angle. -/
def sourceAxis (i : Fin 3) (t : ℝ) : SU2 := ![xElement t, yElement t, zElement t] i

def hilbertAxis (m : ℕ) (i : Fin 3) : Module.End ℂ (HilbertCarrier m) :=
  ![hilbertAxisOne m, hilbertAxisTwo m, hilbertAxisThree m] i

@[simp] theorem sourceAxis_zero (i : Fin 3) : sourceAxis i 0 = 1 := by
  fin_cases i <;> simp [sourceAxis, xElement, ← yConjugator_z]

theorem sourceAxis_hasDerivAt (m : ℕ) (i : Fin 3) (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (sourceAxis i s) v)
      (unitaryAction m (sourceAxis i t) (hilbertAxis m i v)) t := by
  fin_cases i
  · exact x_axis_hilbert_hasDerivAt m v t
  · exact y_axis_hilbert_hasDerivAt m v t
  · exact z_axis_hilbert_hasDerivAt m v t

/-- Right multiplication occurs in the original source group. -/
theorem right_orbit_hasDerivAt (m : ℕ) (i : Fin 3)
    (v : HilbertCarrier m) (g : SU2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (g * sourceAxis i s) v)
      (unitaryAction m (g * sourceAxis i t) (hilbertAxis m i v)) t := by
  let F : HilbertCarrier m →L[ℝ] HilbertCarrier m :=
    ((unitaryAction m g).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ
  have h := F.hasFDerivAt.comp_hasDerivAt t (sourceAxis_hasDerivAt m i v t)
  change HasDerivAt
    (fun s : ℝ => unitaryAction m g (unitaryAction m (sourceAxis i s) v))
    (unitaryAction m g (unitaryAction m (sourceAxis i t) (hilbertAxis m i v))) t at h
  simpa only [unitaryAction_mul_apply] using h

theorem matrixCoefficient_curve_hasDerivAt (m : ℕ) (i : Fin 3)
    (v a : HilbertCarrier m) (g : SU2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matrixCoefficient m v a (g * sourceAxis i s))
      (matrixCoefficient m v (hilbertAxis m i a) (g * sourceAxis i t)) t := by
  simpa only [matrixCoefficient_apply, inner_zero_left, add_zero] using
    HasDerivAt.inner ℂ (hasDerivAt_const t v) (right_orbit_hasDerivAt m i a g t)

/-- The second real derivative along the same actual group curve. -/
theorem matrixCoefficient_curve_second_hasDerivAt (m : ℕ) (i : Fin 3)
    (v a : HilbertCarrier m) (g : SU2) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => deriv (fun r : ℝ => matrixCoefficient m v a (g * sourceAxis i r)) s)
      (matrixCoefficient m v (hilbertAxis m i (hilbertAxis m i a))
        (g * sourceAxis i t)) t := by
  have hfun :
      (fun s : ℝ => deriv (fun r : ℝ => matrixCoefficient m v a (g * sourceAxis i r)) s) =
      fun s => matrixCoefficient m v (hilbertAxis m i a) (g * sourceAxis i s) := by
    funext s
    exact (matrixCoefficient_curve_hasDerivAt m i v a g s).deriv
  rw [hfun]
  exact matrixCoefficient_curve_hasDerivAt m i v (hilbertAxis m i a) g t

/-- An actual pointwise derivative, defined on group functions. -/
def axisDerivative (i : Fin 3) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  deriv (fun t : ℝ => f (g * sourceAxis i t)) 0

def AxisDifferentiable (i : Fin 3) (f : SU2 → ℂ) (g : SU2) : Prop :=
  DifferentiableAt ℝ (fun t : ℝ => f (g * sourceAxis i t)) 0

theorem axisDerivative_add (i : Fin 3) (f h : SU2 → ℂ) (g : SU2)
    (hf : AxisDifferentiable i f g) (hh : AxisDifferentiable i h g) :
    axisDerivative i (fun U => f U + h U) g =
      axisDerivative i f g + axisDerivative i h g :=
  (hf.hasDerivAt.add hh.hasDerivAt).deriv

theorem axisDerivative_const_mul (i : Fin 3) (c : ℂ) (f : SU2 → ℂ) :
    axisDerivative i (fun U => c * f U) = fun U => c * axisDerivative i f U := by
  funext g
  exact deriv_const_mul_field c

theorem axisDerivative_matrixCoefficient (m : ℕ) (i : Fin 3) (v a : HilbertCarrier m) :
    axisDerivative i (matrixCoefficient m v a) = matrixCoefficient m v (hilbertAxis m i a) := by
  funext g
  simpa only [axisDerivative, sourceAxis_zero, mul_one] using
    (matrixCoefficient_curve_hasDerivAt m i v a g 0).deriv

theorem axisDifferentiable_matrixCoefficient (m : ℕ) (i : Fin 3)
    (v a : HilbertCarrier m) (g : SU2) : AxisDifferentiable i (matrixCoefficient m v a) g :=
  (matrixCoefficient_curve_hasDerivAt m i v a g 0).differentiableAt

theorem axisDerivative_twice_matrixCoefficient (m : ℕ) (i : Fin 3)
    (v a : HilbertCarrier m) :
    axisDerivative i (axisDerivative i (matrixCoefficient m v a)) =
      matrixCoefficient m v (hilbertAxis m i (hilbertAxis m i a)) := by
  rw [axisDerivative_matrixCoefficient, axisDerivative_matrixCoefficient]

/-- The round source normalization is determined by the three original
half-angle axes. The definition is independent of representation degrees. -/
def sourceCasimir (f : SU2 → ℂ) (g : SU2) : ℂ :=
  (-4 : ℂ) * ∑ i : Fin 3, axisDerivative i (axisDerivative i f) g

theorem hilbertAxis_casimir_apply (m : ℕ) (a : HilbertCarrier m) :
    (-4 : ℂ) • (∑ i : Fin 3, hilbertAxis m i (hilbertAxis m i a)) =
      ((m : ℂ) * ((m : ℂ) + 2)) • a := by
  have h := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T a)
    (hilbert_axis_casimir m)
  simpa [hilbertAxis, Fin.sum_univ_three, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, add_assoc] using h

theorem matrixCoefficient_casimir_sum (m : ℕ) (v a : HilbertCarrier m) (g : SU2) :
    (-4 : ℂ) * (∑ i : Fin 3,
      matrixCoefficient m v (hilbertAxis m i (hilbertAxis m i a)) g) =
      ((m : ℂ) * ((m : ℂ) + 2)) * matrixCoefficient m v a g := by
  let F : HilbertCarrier m →ₗ[ℂ] ℂ :=
    (innerSL ℂ v).toLinearMap.comp (unitaryAction m g).toLinearEquiv.toLinearMap
  have h := congrArg F (hilbertAxis_casimir_apply m a)
  simp only [map_smul, map_sum, smul_eq_mul] at h
  exact h

/-- The eigenvalue is deduced for the actual differential operator. -/
theorem sourceCasimir_matrixCoefficient (m : ℕ) (v a : HilbertCarrier m) :
    sourceCasimir (matrixCoefficient m v a) =
      fun g => ((m : ℂ) * ((m : ℂ) + 2)) * matrixCoefficient m v a g := by
  funext g
  simp only [sourceCasimir, axisDerivative_twice_matrixCoefficient]
  exact matrixCoefficient_casimir_sum m v a g

theorem sourceCasimir_const_mul (c : ℂ) (f : SU2 → ℂ) :
    sourceCasimir (fun g => c * f g) = fun g => c * sourceCasimir f g := by
  funext g
  simp only [sourceCasimir]
  simp_rw [axisDerivative_const_mul]
  rw [← Finset.mul_sum]
  ring

theorem finset_matrixCoefficient_curve_hasDerivAt {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (v a : ∀ j, HilbertCarrier (m j)) (c : ι → ℂ)
    (i : Fin 3) (g : SU2) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∑ j ∈ s, c j * matrixCoefficient (m j) (v j) (a j) (g * sourceAxis i r))
      (∑ j ∈ s, c j * matrixCoefficient (m j) (v j) (hilbertAxis (m j) i (a j))
        (g * sourceAxis i t)) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact (matrixCoefficient_curve_hasDerivAt (m j) i (v j) (a j) g t).const_mul (c j)

theorem axisDerivative_finset_matrixCoefficients {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (v a : ∀ j, HilbertCarrier (m j)) (c : ι → ℂ) (i : Fin 3) :
    axisDerivative i (fun g => ∑ j ∈ s, c j * matrixCoefficient (m j) (v j) (a j) g) =
      fun g => ∑ j ∈ s,
        c j * matrixCoefficient (m j) (v j) (hilbertAxis (m j) i (a j)) g := by
  funext g
  simpa only [axisDerivative, sourceAxis_zero, mul_one] using
    (finset_matrixCoefficient_curve_hasDerivAt s m v a c i g 0).deriv

/-- Finite sums may mix degrees; each summand retains its derived eigenvalue. -/
theorem sourceCasimir_finset_matrixCoefficients {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (v a : ∀ j, HilbertCarrier (m j)) (c : ι → ℂ) (g : SU2) :
    sourceCasimir (fun U => ∑ j ∈ s, c j * matrixCoefficient (m j) (v j) (a j) U) g =
      ∑ j ∈ s, c j * ((m j : ℂ) * ((m j : ℂ) + 2)) *
        matrixCoefficient (m j) (v j) (a j) g := by
  simp only [sourceCasimir]
  simp_rw [axisDerivative_finset_matrixCoefficients]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  calc
    (-4 : ℂ) * (c j * ∑ i : Fin 3,
        matrixCoefficient (m j) (v j) (hilbertAxis (m j) i (hilbertAxis (m j) i (a j))) g) =
      c j * ((-4 : ℂ) * ∑ i : Fin 3,
        matrixCoefficient (m j) (v j) (hilbertAxis (m j) i (hilbertAxis (m j) i (a j))) g) := by ring
    _ = _ := by rw [matrixCoefficient_casimir_sum]; ring

/-- A finite coefficient record supplies a direct interface to the original
Haar `L²` finite span without a fixed degree or a fixed spectral cutoff. -/
theorem sourceCasimir_finsupp_matrixCoefficients {ι : Type*}
    (m : ι → ℕ) (v a : ∀ j, HilbertCarrier (m j)) (c : ι →₀ ℂ) (g : SU2) :
    sourceCasimir (fun U => c.sum (fun j z => z * matrixCoefficient (m j) (v j) (a j) U)) g =
      c.sum (fun j z => z * ((m j : ℂ) * ((m j : ℂ) + 2)) *
        matrixCoefficient (m j) (v j) (a j) g) := by
  simpa only [Finsupp.sum] using sourceCasimir_finset_matrixCoefficients
    c.support m v a (fun j => c j) g

end GeneratedFoundations.Geometry.SourceCoefficientDifferentiation
