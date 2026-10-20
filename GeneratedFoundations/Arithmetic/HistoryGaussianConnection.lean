module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Geometry.SourceFrameConnection
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The connection of the actual arithmetic Gaussian scale transport

The fibre retains all generated history, phase and source-sector labels up
to the root cutoff. The diagonal generator is the square of the evaluated
positive root. Its exponential is proved to equal the Gaussian multiplier
already acting on that fibre. Thus neither a connection matrix nor a rate is
an additional source input.

At a finite cutoff the Gaussian transport is invertible at every real scale
coordinate. Its infinitesimal connection makes precisely those transported
sections parallel. Arbitrary comparison frames obey the common passive
connection law, with their actual derivatives retained. This scale connection
is not assumed to preserve the fixed coefficient metric: the Gaussian flow
changes that metric, and its transported metric is recorded explicitly.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Operator

namespace GeneratedFoundations.Arithmetic.HistoryGaussianConnection

open HistoryCliffordAction (Index Space Algebra action gaussian historyLift)

def rootEnergy (N : ℕ) (i : Index N) : ℝ :=
  ((i.1.1.val + 1 : ℕ) : ℝ) ^ 2

theorem rootEnergy_pos (N : ℕ) (i : Index N) : 0 < rootEnergy N i := by
  unfold rootEnergy
  positivity

def generator (N : ℕ) : Algebra N :=
  Matrix.diagonal fun i => -(rootEnergy N i : ℂ)

def transportMatrix (N : ℕ) (t : ℝ) : Algebra N :=
  NormedSpace.exp (t • generator N)

theorem gaussian_diagonal (N : ℕ) (t : ℝ) :
    gaussian N t = Matrix.diagonal fun i =>
      (Real.exp (-t * rootEnergy N i) : ℂ) := by
  ext i j
  rcases i with ⟨h, a⟩
  rcases j with ⟨k, b⟩
  by_cases hh : h = k
  · subst k
    by_cases hab : a = b
    · subst b
      simp [gaussian, historyLift, rootEnergy]
    · simp [gaussian, historyLift, hab]
  · simp [gaussian, historyLift, Matrix.one_apply, hh]

/-- The exponential is the existing Gaussian action, including every label. -/
theorem transportMatrix_eq_gaussian (N : ℕ) (t : ℝ) :
    transportMatrix N t = gaussian N t := by
  rw [transportMatrix, generator, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    gaussian_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp, Pi.smul_apply, Complex.real_smul, ← Complex.exp_eq_exp_ℂ]
  rw [show (t : ℂ) * -(rootEnergy N i : ℂ) =
      ((-t * rootEnergy N i : ℝ) : ℂ) by push_cast; ring]
  exact (Complex.ofReal_exp _).symm

@[simp] theorem transportMatrix_zero (N : ℕ) : transportMatrix N 0 = 1 := by
  simp [transportMatrix]

theorem transportMatrix_add (N : ℕ) (s t : ℝ) :
    transportMatrix N (s + t) = transportMatrix N s * transportMatrix N t := by
  have hc : Commute (s • generator N) (t • generator N) :=
    (Commute.refl (generator N)).smul_left s |>.smul_right t
  exact (congrArg NormedSpace.exp (add_smul s t (generator N))).trans
    (NormedSpace.exp_add_of_commute hc)

def operatorRepresentation (N : ℕ) : Algebra N →ₐ[ℂ] (Space N →L[ℂ] Space N) :=
  ((action N).trans (Module.End.toContinuousLinearMap (Space N))).toAlgHom

def transport (N : ℕ) (t : ℝ) : Space N →L[ℂ] Space N :=
  operatorRepresentation N (transportMatrix N t)

@[simp] theorem transport_apply (N : ℕ) (t : ℝ) (x : Space N) (i : Index N) :
    transport N t x i = (Real.exp (-t * rootEnergy N i) : ℂ) * x i := by
  change action N (transportMatrix N t) x i = _
  rw [transportMatrix_eq_gaussian, gaussian_diagonal]
  simp [HistoryCliffordAction.action_apply, Matrix.diagonal_apply]

@[simp] theorem transport_zero (N : ℕ) : transport N 0 = 1 := by
  simp [transport]

theorem transport_add (N : ℕ) (s t : ℝ) :
    transport N (s + t) = transport N s * transport N t := by
  simp only [transport, transportMatrix_add, map_mul]

def frame (N : ℕ) (t : ℝ) : Space N ≃L[ℂ] Space N :=
  ({ toLinearMap := (transport N t).toLinearMap
     invFun := transport N (-t)
     left_inv x := by
       have h := congrArg (fun A : Space N →L[ℂ] Space N => A x)
         (transport_add N (-t) t).symm
       simpa using h
     right_inv x := by
       have h := congrArg (fun A : Space N →L[ℂ] Space N => A x)
         (transport_add N t (-t)).symm
       simpa using h } : Space N ≃ₗ[ℂ] Space N).toContinuousLinearEquiv

@[simp] theorem frame_apply (N : ℕ) (t : ℝ) (x : Space N) :
    frame N t x = transport N t x := rfl

@[simp] theorem frame_symm_apply (N : ℕ) (t : ℝ) (x : Space N) :
    (frame N t).symm x = transport N (-t) x := rfl

/-- Full operator derivative, before applying it to a section. -/
theorem transport_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (transport N) (operatorRepresentation N (generator N) * transport N t) t := by
  let R := (LinearMap.toContinuousLinearMap
    (operatorRepresentation N).toLinearMap).restrictScalars ℝ
  have h := R.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (generator N) t)
  change HasDerivAt (transport N)
    (operatorRepresentation N (generator N * transportMatrix N t)) t at h
  simpa only [map_mul, transport] using h

def connection (N : ℕ) :
    Geometry.SourceFrameConnection.ConnectionForm (B := ℝ) (H := Space N) :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (-operatorRepresentation N (generator N))

@[simp] theorem connection_apply (N : ℕ) (v : ℝ) (x : Space N) :
    connection N v x = -v • operatorRepresentation N (generator N) x := by
  simp [connection]

theorem transported_section_hasDerivAt (N : ℕ) (t : ℝ) (x : Space N) :
    HasDerivAt (fun u => transport N u x)
      (operatorRepresentation N (generator N) (transport N t x)) t := by
  let r := ContinuousLinearMap.restrictScalarsL ℂ (Space N) (Space N) ℝ ℝ
  have h := r.hasFDerivAt.comp_hasDerivAt t (transport_hasDerivAt N t)
  have hx := h.clm_apply (hasDerivAt_const t x)
  change HasDerivAt (fun u => transport N u x)
    (operatorRepresentation N (generator N) (transport N t x) + transport N t 0) t at hx
  simpa only [map_zero, add_zero] using hx

theorem transported_section_parallel (N : ℕ) (t : ℝ) (x : Space N) :
    Geometry.SourceFrameConnection.covariantAt (connection N)
      (fun u => transport N u x) t 1 = 0 := by
  rw [Geometry.SourceFrameConnection.covariantAt,
    (transported_section_hasDerivAt N t x).hasFDerivAt.fderiv]
  simp

def transportedInner (N : ℕ) (t : ℝ) (x y : Space N) : ℂ :=
  inner ℂ (transport N (-t) x) (transport N (-t) y)

theorem transportedInner_preserved (N : ℕ) (t : ℝ) (x y : Space N) :
    transportedInner N t (transport N t x) (transport N t y) = inner ℂ x y := by
  change inner ℂ ((frame N t).symm (frame N t x))
    ((frame N t).symm (frame N t y)) = _
  exact congrArg₂ (inner ℂ) ((frame N t).symm_apply_apply x)
    ((frame N t).symm_apply_apply y)

/-- Parallelism of all native sections already fixes the connection at scale zero. -/
theorem connection_unique (N : ℕ)
    (A : Geometry.SourceFrameConnection.ConnectionForm (B := ℝ) (H := Space N))
    (hA : ∀ x : Space N, Geometry.SourceFrameConnection.covariantAt A
      (fun u => transport N u x) 0 1 = 0) : A = connection N := by
  have h1 : A 1 = -operatorRepresentation N (generator N) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := hA x
    rw [Geometry.SourceFrameConnection.covariantAt,
      (transported_section_hasDerivAt N 0 x).hasFDerivAt.fderiv] at hx
    simp only [transport_zero, one_apply_eq_self,
      ContinuousLinearMap.toSpanSingleton_apply_one] at hx
    change A 1 x = -(operatorRepresentation N (generator N) x)
    exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hx)
  apply ContinuousLinearMap.ext
  intro v
  have hv : A v = v • A 1 := by simpa using A.map_smul v (1 : ℝ)
  rw [hv, h1]
  rfl

/-- The constant connection has zero curvature on its actual one-dimensional base. -/
theorem connection_curvature_zero (N : ℕ) (u v : ℝ) :
    connection N u * connection N v - connection N v * connection N u = 0 := by
  apply sub_eq_zero.mpr
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, connection_apply,
    ContinuousLinearMap.map_smul_of_tower, smul_smul]
  congr 1
  ring

def response (N : ℕ) (t : ℝ) (A : Space N →L[ℂ] Space N) :
    Space N →L[ℂ] Space N := transport N t * A * transport N (-t)

theorem response_intertwines (N : ℕ) (t : ℝ) (A : Space N →L[ℂ] Space N)
    (x : Space N) : response N t A (transport N t x) = transport N t (A x) := by
  change transport N t (A ((frame N t).symm (frame N t x))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem coherent_response_preserved (N : ℕ) (t : ℝ) (A : Space N →L[ℂ] Space N)
    (x y : Space N) :
    transportedInner N t (transport N t x) (response N t A (transport N t y)) =
      inner ℂ x (A y) := by
  rw [response_intertwines, transportedInner_preserved]

/-- Comparison frames use their actual derivatives in the common passive law. -/
theorem passive_covariance {N : ℕ} {G : ℝ → Space N →L[ℂ] Space N}
    {dG : Geometry.SourceFrameConnection.ConnectionForm (B := ℝ) (H := Space N)}
    {f : ℝ → Space N} {df : ℝ →L[ℝ] Space N} {t : ℝ}
    (g : Space N ≃L[ℂ] Space N) (hG : HasFDerivAt G dG t)
    (hg : G t = g.toContinuousLinearMap) (hf : HasFDerivAt f df t) (v : ℝ) :
    Geometry.SourceFrameConnection.covariantAt
      (Geometry.SourceFrameConnection.transformedForm g dG (connection N)) f t v =
      g.symm (Geometry.SourceFrameConnection.covariantAt (connection N)
        (fun u => G u (f u)) t v) :=
  Geometry.SourceFrameConnection.covariantAt_transformed g hG hg hf (connection N) v

structure Conclusions : Prop where
  actual_gaussian : ∀ N t, transportMatrix N t = gaussian N t
  exact_composition : ∀ N s t, transport N (s + t) = transport N s * transport N t
  exact_generator : ∀ N t, HasDerivAt (transport N)
    (operatorRepresentation N (generator N) * transport N t) t
  native_parallelism : ∀ N t (x : Space N),
    Geometry.SourceFrameConnection.covariantAt (connection N)
      (fun u => transport N u x) t 1 = 0
  connection_forced : ∀ N
    (A : Geometry.SourceFrameConnection.ConnectionForm (B := ℝ) (H := Space N)),
    (∀ x : Space N, Geometry.SourceFrameConnection.covariantAt A
      (fun u => transport N u x) 0 1 = 0) → A = connection N
  exact_metric : ∀ N t (x y : Space N),
    transportedInner N t (transport N t x) (transport N t y) = inner ℂ x y
  complete_response : ∀ N t (A : Space N →L[ℂ] Space N) (x y : Space N),
    transportedInner N t (transport N t x) (response N t A (transport N t y)) =
      inner ℂ x (A y)
  scale_curvature : ∀ N u v,
    connection N u * connection N v - connection N v * connection N u = 0

theorem generated : Conclusions where
  actual_gaussian := transportMatrix_eq_gaussian
  exact_composition := transport_add
  exact_generator := transport_hasDerivAt
  native_parallelism := transported_section_parallel
  connection_forced := connection_unique
  exact_metric := transportedInner_preserved
  complete_response := coherent_response_preserved
  scale_curvature := connection_curvature_zero

end GeneratedFoundations.Arithmetic.HistoryGaussianConnection
