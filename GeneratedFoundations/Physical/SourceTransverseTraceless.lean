module

public import GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases

/-!
# The transverse--traceless carrier on the generated spatial directions

The Hermitian determinant readout has one positive and three negative
coordinates.  The three negative coordinates therefore form the spatial
carrier of the generated four-dimensional interface.  For propagation in
the third spatial direction, the transverse--traceless conditions are stated
on symmetric real `3 x 3` tensors themselves.  They are then solved: every
such tensor has a unique plus/cross decomposition.  Thus the two TT
polarizations are an output of the constraints, not an index type supplied
in their definition.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace GeneratedFoundations.Physical.SourceTransverseTraceless

abbrev SpatialIndex := Fin 3
abbrev SpatialTensor := Matrix SpatialIndex SpatialIndex ℝ

/-- Transverse--traceless constraints for propagation along the third
generated spatial coordinate. -/
def IsAxisTT (h : SpatialTensor) : Prop :=
  h.transpose = h ∧ (∀ i, h i 2 = 0) ∧ Matrix.trace h = 0

/-- The matrix with plus amplitude `a` and cross amplitude `b`. -/
def ttMatrix (a b : ℝ) : SpatialTensor :=
  !![a, b, 0;
     b, -a, 0;
     0, 0, 0]

theorem ttMatrix_isAxisTT (a b : ℝ) : IsAxisTT (ttMatrix a b) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ttMatrix, Matrix.transpose_apply]
  · intro i
    fin_cases i <;> simp [ttMatrix]
  · simp [Matrix.trace, Fin.sum_univ_succ, ttMatrix]

theorem axisTT_symmetric {h : SpatialTensor} (hh : IsAxisTT h) (i j : SpatialIndex) :
    h j i = h i j := by
  have hij := congrFun (congrFun hh.1 i) j
  simpa [Matrix.transpose_apply] using hij

theorem axisTT_third_row {h : SpatialTensor} (hh : IsAxisTT h) (j : SpatialIndex) :
    h 2 j = 0 := by
  rw [axisTT_symmetric hh j 2]
  exact hh.2.1 j

theorem axisTT_second_diagonal {h : SpatialTensor} (hh : IsAxisTT h) :
    h 1 1 = -h 0 0 := by
  have h22 : h 2 2 = 0 := hh.2.1 2
  have htr : h 0 0 + (h 1 1 + h 2 2) = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ] using hh.2.2
  linarith

/-- The TT constraints determine the complete tensor from its `00` and `01`
entries. -/
theorem axisTT_eq_ttMatrix {h : SpatialTensor} (hh : IsAxisTT h) :
    h = ttMatrix (h 0 0) (h 0 1) := by
  have hs := axisTT_symmetric hh
  have hr := axisTT_third_row hh
  have hd := axisTT_second_diagonal hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ttMatrix, hh.2.1, hr, hd, hs (0 : SpatialIndex) (1 : SpatialIndex)]

theorem ttMatrix_injective : Function.Injective (fun p : ℝ × ℝ => ttMatrix p.1 p.2) := by
  intro p q hpq
  have h00 := congrFun (congrFun hpq (0 : SpatialIndex)) (0 : SpatialIndex)
  have h01 := congrFun (congrFun hpq (0 : SpatialIndex)) (1 : SpatialIndex)
  apply Prod.ext
  · simpa [ttMatrix] using h00
  · simpa [ttMatrix] using h01

theorem ttMatrix_add (a b c d : ℝ) :
    ttMatrix (a + c) (b + d) = ttMatrix a b + ttMatrix c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ttMatrix, add_comm]

theorem ttMatrix_smul (r a b : ℝ) :
    ttMatrix (r * a) (r * b) = r • ttMatrix a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ttMatrix]

/-- The actual submodule cut out by symmetry, transversality and tracelessness. -/
def ttSubmodule : Submodule ℝ SpatialTensor where
  carrier := {h | IsAxisTT h}
  zero_mem' := by simp [IsAxisTT, Matrix.trace]
  add_mem' := by
    intro h k hh hk
    refine ⟨?_, ?_, ?_⟩
    · simp [Matrix.transpose_add, hh.1, hk.1]
    · intro i
      simp [hh.2.1 i, hk.2.1 i]
    · simp [Matrix.trace_add, hh.2.2, hk.2.2]
  smul_mem' := by
    intro r h hh
    refine ⟨?_, ?_, ?_⟩
    · simp [Matrix.transpose_smul, hh.1]
    · intro i
      simp [hh.2.1 i]
    · simp [Matrix.trace_smul, hh.2.2]

abbrev TTMode := ttSubmodule

def pairToTT : ℝ × ℝ →ₗ[ℝ] TTMode where
  toFun p := ⟨ttMatrix p.1 p.2, ttMatrix_isAxisTT p.1 p.2⟩
  map_add' p q := by
    apply Subtype.ext
    exact ttMatrix_add p.1 p.2 q.1 q.2
  map_smul' r p := by
    apply Subtype.ext
    exact ttMatrix_smul r p.1 p.2

def ttToPair : TTMode →ₗ[ℝ] ℝ × ℝ where
  toFun h := (h.1 0 0, h.1 0 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Constraint solving gives a linear equivalence with two real amplitudes. -/
def ttPairEquiv : TTMode ≃ₗ[ℝ] ℝ × ℝ where
  toLinearMap := ttToPair
  invFun := pairToTT
  left_inv h := by
    apply Subtype.ext
    exact (axisTT_eq_ttMatrix h.2).symm
  right_inv p := by
    ext <;> rfl

theorem ttMode_finrank : Module.finrank ℝ TTMode = 2 := by
  rw [ttPairEquiv.finrank_eq]
  simp [Module.finrank_prod]

def plusPolarization : TTMode := pairToTT (1, 0)
def crossPolarization : TTMode := pairToTT (0, 1)

/-- Every TT tensor has a unique pair of physical polarization amplitudes. -/
theorem existsUnique_polarization (h : SpatialTensor) (hh : IsAxisTT h) :
    ∃! p : ℝ × ℝ, h = ttMatrix p.1 p.2 := by
  refine ⟨(h 0 0, h 0 1), axisTT_eq_ttMatrix hh, ?_⟩
  intro p hp
  apply ttMatrix_injective
  exact hp.symm.trans (axisTT_eq_ttMatrix hh)

structure Properties : Prop where
  constraint_solution : ∀ h : SpatialTensor, IsAxisTT h →
    h = ttMatrix (h 0 0) (h 0 1)
  two_polarizations : Module.finrank ℝ TTMode = 2
  unique_amplitudes : ∀ h : SpatialTensor, IsAxisTT h →
    ∃! p : ℝ × ℝ, h = ttMatrix p.1 p.2

theorem sourceTransverseTracelessProperties : Properties where
  constraint_solution := fun _ => axisTT_eq_ttMatrix
  two_polarizations := ttMode_finrank
  unique_amplitudes := existsUnique_polarization

end GeneratedFoundations.Physical.SourceTransverseTraceless
