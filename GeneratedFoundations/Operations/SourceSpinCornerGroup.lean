module

public import GeneratedFoundations.Operations.SourceSpinCorner
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Complete unitary generation by the source spin corner

The two rotation families are matrix coordinates of the already derived
source operators. Their exponentials are evaluated explicitly. An Euler
factorization is then proved for every determinant-one unitary matrix, with
no Lie-group generation theorem or exponential-surjectivity hypothesis.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner

namespace GeneratedFoundations.Operations.SourceSpinCornerGroup

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

def canonical (a b : ℂ) : Mat2 := !![a, b; -conj b, conj a]

theorem specialUnitary_entries (M : Mat2) (hM : M ∈ SU2) :
    M = canonical (M 0 0) (M 0 1) := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hM
  have ha : Matrix.adjugate M = M.conjTranspose := by
    calc
      Matrix.adjugate M = Matrix.adjugate M * (M * M.conjTranspose) := by
        rw [show M * M.conjTranspose = 1 from hu.2, mul_one]
      _ = (Matrix.adjugate M * M) * M.conjTranspose := (mul_assoc _ _ _).symm
      _ = M.conjTranspose := by rw [Matrix.adjugate_mul, hd, one_smul, one_mul]
  have h11 := congrArg (fun A : Mat2 => A 0 0) ha
  have h10 := congrArg (fun A : Mat2 => A 0 1) ha
  simp [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] at h11 h10
  have h10' : M 1 0 = -conj (M 0 1) := by
    have := congrArg conj h10
    simpa using this.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [canonical, h11, h10']

theorem specialUnitary_norms (M : Mat2) (hM : M ∈ SU2) :
    ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 = 1 := by
  obtain ⟨hu, _⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hM
  have h := congrArg (fun A : Mat2 => (A 0 0).re) hu.2
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Complex.normSq_apply, pow_two] using h

theorem canonical_mem_specialUnitary (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    canonical a b ∈ SU2 := by
  have h' : a * conj a + b * conj b = 1 := by
    rw [Complex.mul_conj', Complex.mul_conj']
    exact_mod_cast h
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonical, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Fin.sum_univ_two, h', mul_comm]
    exact (add_comm _ _).trans h'
  · simpa [canonical, Matrix.det_fin_two] using h'

def zRotation (t : ℝ) : Mat2 :=
  Matrix.diagonal ![Complex.exp (-Complex.I * (t : ℂ) / 2),
    Complex.exp (Complex.I * (t : ℂ) / 2)]

def yRotation (t : ℝ) : Mat2 :=
  !![(Real.cos (t / 2) : ℂ), -(Real.sin (t / 2) : ℂ);
    (Real.sin (t / 2) : ℂ), (Real.cos (t / 2) : ℂ)]

theorem exp_spin3 (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • spinMatrix3) = zRotation t := by
  have h : (Complex.I * (t : ℂ)) • spinMatrix3 =
      Matrix.diagonal ![-Complex.I * (t : ℂ) / 2, Complex.I * (t : ℂ) / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spinMatrix3] <;> ring
  rw [h, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zRotation, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

private def changeBasis : Mat2ˣ where
  val := !![1, 1; Complex.I, -Complex.I]
  inv := !![1 / 2, -Complex.I / 2; 1 / 2, Complex.I / 2]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
    ring_nf
    norm_num
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv] <;> ring_nf <;> norm_num

theorem exp_spin2 (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • spinMatrix2) = yRotation t := by
  have h : (Complex.I * (t : ℂ)) • spinMatrix2 =
      (changeBasis : Mat2) * ((Complex.I * (t : ℂ)) • spinMatrix3) *
        (↑(changeBasis⁻¹) : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [changeBasis, spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring
  rw [h, Matrix.exp_units_conj, exp_spin3]
  have hp : Complex.exp (Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) + (Real.sin (t / 2) : ℂ) * Complex.I := by
    convert Complex.exp_ofReal_mul_I (t / 2) using 1
    congr 1
    push_cast
    ring
  have hm : Complex.exp (-Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) - (Real.sin (t / 2) : ℂ) * Complex.I := by
    convert Complex.exp_ofReal_mul_I (-(t / 2)) using 1
    · congr 1
      push_cast
      ring
    · simp [sub_eq_add_neg]
  unfold zRotation
  rw [hp, hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, changeBasis, yRotation,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals ring_nf <;> norm_num

theorem zRotation_mem (t : ℝ) : zRotation t ∈ SU2 := by
  have h : zRotation t = canonical (Complex.exp (-Complex.I * (t : ℂ) / 2)) 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zRotation, canonical, ← Complex.exp_conj, map_ofNat]
  rw [h]
  apply canonical_mem_specialUnitary
  simp [Complex.norm_exp]

theorem yRotation_mem (t : ℝ) : yRotation t ∈ SU2 := by
  have h : yRotation t = canonical (Real.cos (t / 2)) (-Real.sin (t / 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-Complex.ofReal_cos, -Complex.ofReal_sin, yRotation, canonical]
  rw [h]
  apply canonical_mem_specialUnitary
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_neg, sq_abs, add_comm] using
    Real.sin_sq_add_cos_sq (t / 2)

theorem zRotation_add (s t : ℝ) : zRotation (s + t) = zRotation s * zRotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zRotation, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  all_goals
    congr 1
    ring

theorem euler_entries (a b c : ℝ) :
    zRotation a * yRotation b * zRotation c =
      canonical
        (Complex.exp (-Complex.I * ((a + c : ℝ) : ℂ) / 2) * Real.cos (b / 2))
        (-Complex.exp (-Complex.I * ((a - c : ℝ) : ℂ) / 2) * Real.sin (b / 2)) := by
  have hs : -Complex.I * ((a + c : ℝ) : ℂ) / 2 =
      -Complex.I * a / 2 + -Complex.I * c / 2 := by push_cast; ring
  have hd : -Complex.I * ((a - c : ℝ) : ℂ) / 2 =
      -Complex.I * a / 2 + Complex.I * c / 2 := by push_cast; ring
  rw [hs, hd, Complex.exp_add, Complex.exp_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, zRotation, yRotation, canonical,
      Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_conj, map_ofNat]
  all_goals ring

/-- Every determinant-one unitary is a product of three actual spin-axis exponentials. -/
theorem euler_factorization (M : Mat2) (hM : M ∈ SU2) :
    ∃ a b c : ℝ, M = zRotation a * yRotation b * zRotation c := by
  let u := M 0 0
  let v := M 0 1
  have huv : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := specialUnitary_norms M hM
  have hu : ‖u‖ ≤ 1 := by nlinarith [sq_nonneg ‖v‖, norm_nonneg u]
  let a := -u.arg - (-v).arg
  let b := 2 * Real.arccos ‖u‖
  let c := -u.arg + (-v).arg
  refine ⟨a, b, c, ?_⟩
  rw [euler_entries, specialUnitary_entries M hM]
  have hc : Real.cos (b / 2) = ‖u‖ := by
    dsimp [b]
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.cos_arccos (by linarith [norm_nonneg u]) hu
  have hs : Real.sin (b / 2) = ‖v‖ := by
    dsimp [b]
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sin_arccos]
    rw [show 1 - ‖u‖ ^ 2 = ‖v‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg v)]
  have ha : -Complex.I * ((a + c : ℝ) : ℂ) / 2 = (u.arg : ℂ) * Complex.I := by
    dsimp [a, c]
    push_cast
    ring
  have hv : -Complex.I * ((a - c : ℝ) : ℂ) / 2 = ((-v).arg : ℂ) * Complex.I := by
    dsimp [a, c]
    push_cast
    ring
  rw [hc, hs, ha, hv]
  congr 1
  · simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I u).symm
  · have h := Complex.norm_mul_exp_arg_mul_I (-v)
    simpa [norm_neg, mul_comm, neg_mul] using congrArg Neg.neg h.symm

theorem source_axes_generate_all (M : Mat2) (hM : M ∈ SU2) :
    ∃ a b c : ℝ,
      M = NormedSpace.exp ((Complex.I * a) • spinMatrix3) *
        NormedSpace.exp ((Complex.I * b) • spinMatrix2) *
        NormedSpace.exp ((Complex.I * c) • spinMatrix3) := by
  simpa only [exp_spin3, exp_spin2] using euler_factorization M hM

def zElement (t : ℝ) : SU2 := ⟨zRotation t, zRotation_mem t⟩
def yElement (t : ℝ) : SU2 := ⟨yRotation t, yRotation_mem t⟩

/-- Algebraic generation, with no topological closure or density qualification. -/
theorem generated_subgroup_eq_top :
    Subgroup.closure (Set.range zElement ∪ Set.range yElement) = ⊤ := by
  apply top_unique
  intro U _
  obtain ⟨a, b, c, h⟩ := euler_factorization U.val U.property
  have hu : U = zElement a * yElement b * zElement c := Subtype.ext h
  rw [hu]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨b, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

end GeneratedFoundations.Operations.SourceSpinCornerGroup
