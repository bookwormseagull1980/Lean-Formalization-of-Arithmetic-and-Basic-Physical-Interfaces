module

public import GeneratedFoundations.Physical.SourceTTResponse
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import GeneratedFoundations.Physical.SourceConformalResponse

/-!
# The V5 TT-endpoint Yang--Mills model (certificate-conditional)

This module is the explicit home of the **V5 TT-endpoint** closure.  It is
parameterized by a `SourceTTResponse.EndpointCertificate`; it is deliberately
not a field of the zero-argument `CommonFoundation.Conclusions`.

The zero-argument Lean physical branch uses the Gaussian IR edge
`sqrt(2*pi)` (`CanonicalYangMills`).  V5 uses the finite-response TT endpoint
`kL`, which is strictly below that edge.  The two models are therefore kept
in separate modules and are never identified:

* `CanonicalYangMills` — IR-edge closure, unconditional, zero-argument.
* `CanonicalYangMillsTT` — V5 TT-endpoint closure, conditional on the
  certified endpoint.

The companion V5 computation supplies the numerical certificate; this module
only proves the Yang--Mills consequence at the certified endpoint.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.CanonicalYangMillsTT

open SourceTTResponse SourceGeneratedYangMillsAction SourceGeneratedYangMillsGap
open SourceConformalResponse

/-- The condensed amplitude at the certified TT endpoint. -/
def amplitude (cert : EndpointCertificate) : ℝ :=
  condensedAmplitude cert.L cert.aboveCritical

/-- The dimensionless Yang--Mills gap at the certified TT endpoint. -/
def gapSq (cert : EndpointCertificate) : ℝ :=
  generatedYangMillsGapSq cert.L (amplitude cert)

/-- The V5 TT-endpoint Yang--Mills conclusion, conditional on the certificate. -/
structure Conclusions (cert : EndpointCertificate) : Prop where
  endpoint_equation : SourceTTGaussianCoefficient.response cert.L = 4 / 27
  endpoint_identified : cert.L = SourceTTGaussianCoefficient.radius
  endpoint_below_ir_edge : cert.L < Real.sqrt (2 * Real.pi)
  condensed : 0 < amplitude cert ∧
    completeResponse (amplitude cert) = generatedTarget cert.L
  positive_gap : 0 < gapSq cert

theorem generated (cert : EndpointCertificate) : Conclusions cert where
  endpoint_equation := cert.endpointEquation
  endpoint_identified := L_eq_radius cert
  endpoint_below_ir_edge := cert.belowIR
  condensed := by
    have h := condensedAmplitude_spec cert.L cert.aboveCritical
    exact ⟨h.1, h.2.1⟩
  positive_gap := by
    have h := condensedAmplitude_spec cert.L cert.aboveCritical
    exact h.2.2

end GeneratedFoundations.Physical.CanonicalYangMillsTT
