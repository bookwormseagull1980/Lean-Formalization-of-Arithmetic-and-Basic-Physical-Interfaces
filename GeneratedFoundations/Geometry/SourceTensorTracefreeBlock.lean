module

public import GeneratedFoundations.Geometry.SourceTensorSpectralCore

/-!
# The derived symmetric trace-free tensor carrier

Symmetry and zero trace define a subspace of the nine original tensor
components. Five independent component functions give an explicit linear
equivalence with that constraint kernel. Its dimension follows from this
equivalence. The original covariant rough operator preserves the kernel,
so its restriction inherits symmetry and the exact connection energy.

Transversality remains the differential constraint on this same carrier;
no transverse spectrum is assumed in constructing the trace-free space.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorSpectralCore

namespace GeneratedFoundations.Geometry.SourceTensorTracefreeBlock

def tracefreeSpace (m : ℕ) : Submodule ℂ (TensorBlock m) where
  carrier := {H | (∀ a b : Fin 3, H (a, b) = H (b, a)) ∧
    (∑ a : Fin 3, H (a, a)) = 0}
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  add_mem' := by
    intro H K hH hK
    constructor
    · intro a b
      change H (a, b) + K (a, b) = H (b, a) + K (b, a)
      rw [hH.1, hK.1]
    · change (∑ a : Fin 3, (H (a, a) + K (a, a))) = 0
      rw [Finset.sum_add_distrib, hH.2, hK.2, add_zero]
  smul_mem' := by
    intro c H hH
    constructor
    · intro a b
      change c • H (a, b) = c • H (b, a)
      rw [hH.1]
    · change (∑ a : Fin 3, c • H (a, a)) = 0
      rw [← Finset.smul_sum, hH.2, smul_zero]

def assemble (m : ℕ) : (Fin 5 → HilbertCarrier m) →ₗ[ℂ] TensorBlock m where
  toFun c := WithLp.toLp 2 (fun ab =>
    ![![c 0, c 1, c 2], ![c 1, c 3, c 4],
      ![c 2, c 4, -c 0 - c 3]] ab.1 ab.2)
  map_add' c d := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    rcases ab with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> (simp <;> module)
  map_smul' z c := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    rcases ab with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> (simp <;> module)

theorem assemble_mem (m : ℕ) (c : Fin 5 → HilbertCarrier m) :
    assemble m c ∈ tracefreeSpace m := by
  constructor
  · intro a b
    fin_cases a <;> fin_cases b <;> rfl
  · change (∑ a : Fin 3,
      ![![c 0, c 1, c 2], ![c 1, c 3, c 4],
        ![c 2, c 4, -c 0 - c 3]] a a) = 0
    rw [Fin.sum_univ_three]
    change c 0 + c 3 + (-c 0 - c 3) = 0
    module

def extract (m : ℕ) : tracefreeSpace m →ₗ[ℂ] (Fin 5 → HilbertCarrier m) where
  toFun H := ![H.val (0, 0), H.val (0, 1), H.val (0, 2),
    H.val (1, 1), H.val (1, 2)]
  map_add' H K := by
    funext j
    fin_cases j <;> rfl
  map_smul' z H := by
    funext j
    fin_cases j <;> rfl

theorem assemble_extract (m : ℕ) (H : tracefreeSpace m) :
    assemble m (extract m H) = (H : TensorBlock m) := by
  have hs := H.property.1
  have ht : H.val (0, 0) + H.val (1, 1) + H.val (2, 2) = 0 := by
    simpa only [Fin.sum_univ_three] using H.property.2
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
  funext ab
  rcases ab with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    change _ = H.val (_, _)
  all_goals try rfl
  all_goals try exact hs _ _
  all_goals change -H.val (0, 0) - H.val (1, 1) = H.val (2, 2)
  all_goals
    calc
      _ = -(H.val (0, 0) + H.val (1, 1)) := by module
      _ = H.val (2, 2) := (eq_neg_of_add_eq_zero_right ht).symm

def tracefreeEquiv (m : ℕ) :
    (Fin 5 → HilbertCarrier m) ≃ₗ[ℂ] tracefreeSpace m where
  toLinearMap := (assemble m).codRestrict (tracefreeSpace m) (assemble_mem m)
  invFun := extract m
  left_inv c := by
    funext j
    fin_cases j <;> rfl
  right_inv H := Subtype.ext (assemble_extract m H)

theorem tracefree_finrank (m : ℕ) :
    Module.finrank ℂ (tracefreeSpace m) = 5 * (m + 1) := by
  rw [← (tracefreeEquiv m).finrank_eq]
  simp [Module.finrank_pi_fintype, hilbertCarrier_finrank]

theorem rough_mem (m : ℕ) (H : tracefreeSpace m) :
    roughBlock m (H : TensorBlock m) ∈ tracefreeSpace m := by
  constructor
  · intro a b
    rw [roughBlock_component, roughBlock_component]
    exact rough_symmetric m _ H.property.1 a b
  · simp only [roughBlock_component]
    exact rough_trace_zero m _ H.property.2

def roughTracefree (m : ℕ) : Module.End ℂ (tracefreeSpace m) where
  toFun H := ⟨roughBlock m H, rough_mem m H⟩
  map_add' H K := Subtype.ext ((roughBlock m).map_add H K)
  map_smul' c H := Subtype.ext ((roughBlock m).map_smul c H)

theorem roughTracefree_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := tracefreeSpace m) (roughTracefree m) := by
  intro H K
  exact roughBlock_symmetric m H K

theorem roughTracefree_energy (m : ℕ) (H : tracefreeSpace m) :
    (inner ℂ H (roughTracefree m H)).re =
      ∑ i : Fin 3, ‖covariantBlock m i (H : TensorBlock m)‖ ^ 2 :=
  roughBlock_energy m H

end GeneratedFoundations.Geometry.SourceTensorTracefreeBlock
