module

public import GeneratedFoundations.Geometry.SourceTensorTTResolvent
public import GeneratedFoundations.Geometry.SourceTensorTTWitness

/-!
# Exhaustion and sharp lower edge of the projective TT spectrum

The differential identity supplies the possible branches. Actual
homogeneous polynomial witnesses supply every required eigenvalue. The
bounded resolvents exclude any additional spectrum in the full TT field.
The resulting labels are a conclusion of the original differential, not
an input used to define its action.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators LinearPMap
open GeneratedFoundations.Geometry.SourceTensorTTBlock
open GeneratedFoundations.Geometry.SourceTensorTTBranches
open GeneratedFoundations.Geometry.SourceTensorTTField
open GeneratedFoundations.Geometry.SourceTensorTTResolvent
open GeneratedFoundations.Geometry.SourceTensorTTWitness

namespace GeneratedFoundations.Geometry.SourceTensorTTSpectrum

theorem block_eigenvalue_label {m : ℕ} (hm : Even m)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    ∃ k : ℕ, Even k ∧ 2 ≤ k ∧
      ttCurlEigenvalue m j ^ 2 - 3 = (k : ℝ) * ((k : ℝ) + 2) - 2 := by
  rcases tt_eigenvalue_cases m j with hp | hn
  · refine ⟨m + 2, hm.add (by decide : Even 2), by omega, ?_⟩
    rw [hp]
    push_cast
    ring
  · have hge := tt_rough_eigenvalue_ge_six hm j
    rw [hn] at hge
    have hm4 : 4 ≤ m := by
      by_contra h
      have hm3 : (m : ℝ) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm3)]
    have hsub : 2 ≤ m := by omega
    have heven : Even (m - 2) := by
      obtain ⟨r, hr⟩ := hm
      exact ⟨r - 1, by omega⟩
    refine ⟨m - 2, heven, by omega, ?_⟩
    rw [hn, Nat.cast_sub hsub]
    norm_num
    ring

theorem eigenvalue_label (a : TTIndex) :
    ∃ k : ℕ, Even k ∧ 2 ≤ k ∧
      roughEigenvalue a = (k : ℝ) * ((k : ℝ) + 2) - 2 :=
  block_eigenvalue_label a.1.1.property a.2

theorem label_present {k : ℕ} (hk : 2 ≤ k) (he : Even k) :
    ∃ a : TTIndex,
      roughEigenvalue a = (k : ℝ) * ((k : ℝ) + 2) - 2 := by
  have hm : Even (k - 2) := by
    obtain ⟨r, hr⟩ := he
    exact ⟨r - 1, by omega⟩
  obtain ⟨j, hj⟩ := upper_branch_present (k - 2)
  let row : SourceTensorHilbertSum.RowIndex := ⟨⟨k - 2, hm⟩, ⟨0, by omega⟩⟩
  refine ⟨⟨row, j⟩, ?_⟩
  change ttCurlEigenvalue (k - 2) j ^ 2 - 3 = _
  rw [hj, Nat.cast_sub hk]
  norm_num
  ring

/-- Both presence and exhaustion refer to the full closed differential
operator on the original projective TT field. -/
theorem spectrum_labels (z : ℂ) :
    z ∈ SourceTensorTTResolvent.spectrum ↔ ∃ k : ℕ, Even k ∧ 2 ≤ k ∧
      z = (((k : ℝ) * ((k : ℝ) + 2) - 2 : ℝ) : ℂ) := by
  rw [mem_spectrum_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, he, hk, hvalue⟩ := eigenvalue_label a
    exact ⟨k, he, hk, congrArg Complex.ofReal hvalue⟩
  · rintro ⟨k, he, hk, rfl⟩
    obtain ⟨a, ha⟩ := label_present hk he
    exact ⟨a, (congrArg Complex.ofReal ha).symm⟩

theorem spectral_bottom :
    (6 : ℂ) ∈ SourceTensorTTResolvent.spectrum ∧
      ∀ z : ℂ, z ∈ SourceTensorTTResolvent.spectrum → 6 ≤ z.re := by
  constructor
  · rw [spectrum_labels]
    exact ⟨2, by decide, le_rfl, by norm_num⟩
  · intro z hz
    obtain ⟨a, rfl⟩ := (mem_spectrum_iff z).mp hz
    simpa only [Complex.ofReal_re] using roughEigenvalue_ge_six a

end GeneratedFoundations.Geometry.SourceTensorTTSpectrum
