module

public import GeneratedFoundations.Arithmetic.HistoryCentrePotential

/-!
# Normalization of the actual one-dimensional centre response

The variance is differentiated from the complete source partition. Its
positive square root determines the score normalization. The normalized
response line and the constant line have a unique complex-linear unitary
which preserves their generated unit vectors. Their scalar evolutions
intertwine, with the rate given by that same variance.

The response variable is a configuration coordinate. In the closed source
its value is the previously proved equilibrium, so the rate equals one.
No physical connection multiplicity or physical score normalization is
inserted in the arithmetic source.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryCentreNormalization

def variance (n : ℕ) (h : ℝ) : ℝ := HistoryJointCentreResponse.susceptibility n h

theorem variance_pos (n : ℕ) (h : ℝ) : 0 < variance n h :=
  HistoryJointCentreResponse.susceptibility_pos n h

def scoreScale (n : ℕ) (h : ℝ) : ℝ := (Real.sqrt (variance n h))⁻¹

theorem scoreScale_pos (n : ℕ) (h : ℝ) : 0 < scoreScale n h :=
  inv_pos.mpr (Real.sqrt_pos.mpr (variance_pos n h))

def normalizedIncrement (n : ℕ) (h v : ℝ) : ℝ := scoreScale n h * v

theorem normalizedIncrement_scale (n : ℕ) (h v t : ℝ) :
    normalizedIncrement n h (t * v) = t * normalizedIncrement n h v := by
  unfold normalizedIncrement
  ring

theorem scoreScale_sq_mul_variance (n : ℕ) (h : ℝ) :
    scoreScale n h ^ 2 * variance n h = 1 := by
  rw [scoreScale, inv_pow, Real.sq_sqrt (variance_pos n h).le,
    inv_mul_cancel₀ (variance_pos n h).ne']

theorem variance_equilibrium (n : ℕ) :
    variance n (HistoryCentrePotential.equilibrium n) = 1 :=
  HistoryJointCentreResponse.closed_susceptibility n

theorem scoreScale_equilibrium (n : ℕ) :
    scoreScale n (HistoryCentrePotential.equilibrium n) = 1 := by
  rw [scoreScale, variance_equilibrium, Real.sqrt_one, inv_one]

abbrev ResponseLine := ℂ

/-- The derivative of the actual restoring force, projected onto the
normalized score at the specified configuration. -/
def responseProjection (n : ℕ) (h : ℝ) : ℝ := variance n h * scoreScale n h

theorem responseProjection_pos (n : ℕ) (h : ℝ) : 0 < responseProjection n h :=
  mul_pos (variance_pos n h) (scoreScale_pos n h)

theorem normalizedForce_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (fun u => scoreScale n h * HistoryCentrePotential.force n u)
      (responseProjection n h) h := by
  simpa only [responseProjection, variance, mul_comm] using
    (HistoryCentrePotential.force_hasDerivAt n h).const_mul (scoreScale n h)

abbrev ConstantLine := ℂ

def responseToConstant : ResponseLine ≃ₗᵢ[ℂ] ConstantLine :=
  LinearIsometryEquiv.refl ℂ ℂ

theorem responseToConstant_generator : responseToConstant 1 = 1 := rfl

theorem responseToConstant_unique (U : ResponseLine ≃ₗᵢ[ℂ] ConstantLine)
    (hU : U 1 = 1) : U = responseToConstant := by
  apply LinearIsometryEquiv.ext
  intro z
  calc
    U z = U (z • (1 : ℂ)) := by simp
    _ = z • U 1 := U.map_smul z 1
    _ = responseToConstant z := by simp [hU, responseToConstant]

def evolution (n : ℕ) (h t : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-t * variance n h) : ℂ) * z

theorem evolution_zero (n : ℕ) (h : ℝ) (z : ℂ) : evolution n h 0 z = z := by
  simp [evolution]

theorem evolution_add (n : ℕ) (h t u : ℝ) (z : ℂ) :
    evolution n h (t + u) z = evolution n h t (evolution n h u z) := by
  simp only [evolution, neg_add, add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc]

theorem responseToConstant_intertwines (n : ℕ) (h t : ℝ) (z : ResponseLine) :
    responseToConstant (evolution n h t z) =
      evolution n h t (responseToConstant z) := rfl

theorem evolution_equilibrium (n : ℕ) (t : ℝ) (z : ℂ) :
    evolution n (HistoryCentrePotential.equilibrium n) t z =
      (Real.exp (-t) : ℂ) * z := by
  rw [evolution, variance_equilibrium, mul_one]

structure Conclusions : Prop where
  actual_variance_positive : ∀ n h, 0 < variance n h
  exact_score_normalization : ∀ n h, scoreScale n h ^ 2 * variance n h = 1
  generated_equilibrium_variance : ∀ n,
    variance n (HistoryCentrePotential.equilibrium n) = 1
  unique_normalized_unitary : ∀ U : ResponseLine ≃ₗᵢ[ℂ] ConstantLine,
    U 1 = 1 → U = responseToConstant
  actual_intertwining : ∀ n h t z, responseToConstant (evolution n h t z) =
    evolution n h t (responseToConstant z)
  closed_source_rate : ∀ n t z,
    evolution n (HistoryCentrePotential.equilibrium n) t z = (Real.exp (-t) : ℂ) * z

theorem generated : Conclusions where
  actual_variance_positive := variance_pos
  exact_score_normalization := scoreScale_sq_mul_variance
  generated_equilibrium_variance := variance_equilibrium
  unique_normalized_unitary := responseToConstant_unique
  actual_intertwining := responseToConstant_intertwines
  closed_source_rate := evolution_equilibrium

end GeneratedFoundations.Arithmetic.HistoryCentreNormalization
