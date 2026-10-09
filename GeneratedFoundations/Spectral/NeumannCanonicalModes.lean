module

public import GeneratedFoundations.Spectral.NeumannSpectralDomain

/-!
# The canonical representative of each Neumann eigenline

The left endpoint is evaluated through the unique continuous Sobolev trace.
Unit norm and a strictly positive real left trace select one vector from each
complex eigenline. Uniqueness is in the original interval Hilbert space, not
among extensions of representatives outside the interval.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

def neumannLeftTrace (f : (complexNeumannOperator hL.out).domain) : ℂ :=
  (complexNeumannRepresentative f).value 0

theorem neumannLeftTrace_on_representative (f : ComplexH2Representative 0 L)
    (hf : IsComplexNeumann f) :
    neumannLeftTrace L ⟨f.toL2, f, hf, rfl⟩ = f.value 0 :=
  (ComplexH2Representative.trace_unique hL.out
    (complexNeumannRepresentative_spec ⟨f.toL2, f, hf, rfl⟩).2).1 ⟨le_rfl, hL.out.le⟩

theorem neumannLeftTrace_smul (c : ℂ) (f : (complexNeumannOperator hL.out).domain) :
    neumannLeftTrace L (c • f) = c * neumannLeftTrace L f := by
  have heq : (complexNeumannRepresentative (c • f)).toL2 =
      ((complexNeumannRepresentative f).smul c).toL2 := by
    rw [(complexNeumannRepresentative_spec (c • f)).2,
      ComplexH2Representative.toL2_smul, (complexNeumannRepresentative_spec f).2]
    rfl
  exact (ComplexH2Representative.trace_unique hL.out heq).1 ⟨le_rfl, hL.out.le⟩

def neumannCosineDomainVector (n : ℕ) : (complexNeumannOperator hL.out).domain :=
  ⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩

def neumannModeEndpoint : ℕ → ℝ
  | 0 => (Real.sqrt L)⁻¹
  | _ + 1 => (Real.sqrt L)⁻¹ * Real.sqrt 2

theorem neumannModeEndpoint_pos (n : ℕ) : 0 < neumannModeEndpoint L n := by
  cases n with
  | zero => exact inv_pos.mpr (Real.sqrt_pos.mpr hL.out)
  | succ n =>
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hL.out))
      (Real.sqrt_pos.mpr (by norm_num))

theorem neumannLeftTrace_cosine (n : ℕ) :
    neumannLeftTrace L (neumannCosineDomainVector L n) = (neumannModeEndpoint L n : ℂ) := by
  have heq : neumannCosineDomainVector L n =
      (⟨(neumannCosineRepresentative L n).toL2,
        neumannCosineRepresentative L n, neumannCosineRepresentative_neumann L n, rfl⟩ :
          (complexNeumannOperator hL.out).domain) :=
    Subtype.ext (neumannCosineRepresentative_toL2 L n).symm
  rw [heq, neumannLeftTrace_on_representative L (neumannCosineRepresentative L n)
    (neumannCosineRepresentative_neumann L n)]
  cases n with
  | zero => simp [neumannCosineRepresentative, neumannModeEndpoint, ComplexH2Representative.constant]
  | succ n => simp [neumannCosineRepresentative, neumannModeEndpoint, ComplexH2Representative.smul,
      cosineH2Representative]

/-- Positivity fixes the complex phase as well as the real sign. -/
theorem neumannCanonicalMode_unique (n : ℕ) (f : (complexNeumannOperator hL.out).domain)
    (heig : complexNeumannOperator hL.out f =
      (neumannEigenvalue L n : ℂ) • (f : ComplexIntervalL2 0 L))
    (hnorm : ‖(f : ComplexIntervalL2 0 L)‖ = 1)
    (hpositive : ∃ r : ℝ, 0 < r ∧ neumannLeftTrace L f = (r : ℂ)) :
    f = neumannCosineDomainVector L n := by
  obtain ⟨c, hc⟩ := (complexNeumann_eigenvector_iff L n f).mp heig
  have hsub : f = c • neumannCosineDomainVector L n := Subtype.ext hc
  have htrace : neumannLeftTrace L f = c * (neumannModeEndpoint L n : ℂ) := by
    rw [hsub, neumannLeftTrace_smul, neumannLeftTrace_cosine]
  rw [hc, norm_smul, (neumannCosineMode_orthonormal L).norm_eq_one n, mul_one] at hnorm
  obtain ⟨r, hr, hfr⟩ := hpositive
  have ha : (neumannModeEndpoint L n : ℂ) ≠ 0 := by
    exact_mod_cast (neumannModeEndpoint_pos L n).ne'
  have hcvalue : c = ((r / neumannModeEndpoint L n : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    exact (eq_div_iff ha).mpr (htrace.symm.trans hfr)
  have hratio : r / neumannModeEndpoint L n = 1 := by
    simpa only [hcvalue, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hr (neumannModeEndpoint_pos L n))] using hnorm
  have hc1 : c = 1 := by rw [hcvalue, hratio, Complex.ofReal_one]
  simpa only [hc1, one_smul] using hsub

theorem neumannCanonicalMode_existsUnique (n : ℕ) :
    ∃! f : (complexNeumannOperator hL.out).domain,
      complexNeumannOperator hL.out f =
        (neumannEigenvalue L n : ℂ) • (f : ComplexIntervalL2 0 L) ∧
      ‖(f : ComplexIntervalL2 0 L)‖ = 1 ∧
      ∃ r : ℝ, 0 < r ∧ neumannLeftTrace L f = (r : ℂ) := by
  refine ⟨neumannCosineDomainVector L n, ?_, ?_⟩
  · exact ⟨complexNeumannOperator_cosine L n, (neumannCosineMode_orthonormal L).norm_eq_one n,
      neumannModeEndpoint L n, neumannModeEndpoint_pos L n, neumannLeftTrace_cosine L n⟩
  · intro f hf
    exact neumannCanonicalMode_unique L n f hf.1 hf.2.1 hf.2.2

end GeneratedFoundations.Spectral
