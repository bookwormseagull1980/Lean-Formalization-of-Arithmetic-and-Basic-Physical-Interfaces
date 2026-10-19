module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import GeneratedFoundations.Physical.SourceInternalYangMillsResponse
public import GeneratedFoundations.Physical.SourceTTGaussianCoefficient
public import GeneratedFoundations.Physical.SourceTTEndpointInterval
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The V5 finite-response TT endpoint (certificate interface)

This module makes the **model distinction** explicit.  The zero-argument Lean
physical branch uses the infrared *edge* of the Gaussian correlation window,
`sqrt(2*pi)`, as its canonical internal radius.  V5 uses a different closure:
the finite-response TT endpoint `kL`, the root of the TT spectral-sum equation
`A(L)=4/27` at the self-consistent emergence scale.

The spectral coefficient is the eight-branch Gaussian integral defined in
`SourceTTGaussianCoefficient`. `EndpointCertificate` binds the endpoint to
that integral and records its two geometric bounds. The companion
`CanonicalYangMillsTT` module proves the Yang--Mills statements at this
certified radius. It is deliberately **not**
part of `CommonFoundation.Conclusions`, so the zero-argument IR-edge theorem
and the certificate-conditional TT model are never mixed.

At the IR edge the TT sum is about `0.147374`, below `4/27`; the certificate's
`belowIR` field is therefore a genuine separation of the two closures, not a
numerical convention.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceTTResponse

open SourceGeneratedYangMillsGap SourceInternalYangMillsResponse

/-- A certified V5 finite-response TT endpoint.

The fields `L_pos`, `aboveCritical` and `belowIR` place the endpoint strictly
inside the condensed branch and strictly below the Gaussian IR edge.  The
`endpointEquation` refers to the actual spectral integral evaluated at `L`;
there is no independent response value in the certificate. -/
structure EndpointCertificate where
  L : ℝ
  L_pos : 0 < L
  aboveCritical : criticalRadius < L
  belowIR : L < Real.sqrt (2 * Real.pi)
  endpointEquation : SourceTTGaussianCoefficient.response L = 4 / 27

/-- Every valid endpoint certificate describes the same integral-defined
radius; a certificate cannot select a different positive endpoint. -/
theorem L_eq_radius (cert : EndpointCertificate) :
    cert.L = SourceTTGaussianCoefficient.radius :=
  (SourceTTGaussianCoefficient.response_eq_iff cert.L_pos).mp cert.endpointEquation

theorem endpoint_unique (a b : EndpointCertificate) : a.L = b.L := by
  rw [L_eq_radius a, L_eq_radius b]

/-- Construct the geometric endpoint certificate from an enclosure of the
actual integral. The enclosure controls the location of an already uniquely
defined radius; it does not supply a new endpoint or response number. -/
def endpointCertificateOfBounds (b : SourceTTEndpointInterval.CoefficientBounds)
    (hlo : criticalRadius < SourceTTEndpointInterval.rootLower b)
    (hhi : SourceTTEndpointInterval.rootUpper b < Real.sqrt (2 * Real.pi)) :
    EndpointCertificate where
  L := SourceTTGaussianCoefficient.radius
  L_pos := SourceTTGaussianCoefficient.radius_pos
  aboveCritical := hlo.trans_le (SourceTTEndpointInterval.generated b).root_lower
  belowIR := lt_of_le_of_lt (SourceTTEndpointInterval.generated b).root_upper hhi
  endpointEquation := SourceTTGaussianCoefficient.response_radius

/-- The certified TT endpoint is strictly below the Gaussian IR edge. -/
theorem L_lt_irEdge (cert : EndpointCertificate) :
    cert.L < Real.sqrt (2 * Real.pi) :=
  cert.belowIR

/-- The certified TT endpoint is not the IR edge. -/
theorem L_ne_irEdge (cert : EndpointCertificate) :
    cert.L ≠ Real.sqrt (2 * Real.pi) :=
  ne_of_lt cert.belowIR

/-- The certified TT endpoint lies strictly above the critical ratio. -/
theorem critical_lt_L (cert : EndpointCertificate) :
    criticalRadius < cert.L :=
  cert.aboveCritical

end GeneratedFoundations.Physical.SourceTTResponse
