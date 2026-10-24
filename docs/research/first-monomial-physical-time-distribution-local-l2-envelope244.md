# Physical momentum distributions from spatial L² envelopes

Base commit `63fbcaa3` (*reduce physical momentum distributions to spatial equicontinuity*).

The existing compact-tested old time differentiation theorem assumes a spatial
L¹ majorant valid throughout a neighborhood of each elapsed time. Previous
PDE-side criteria achieved it using **pointwise** uniform bounds or spatial
equicontinuity. The new criterion instead assumes a spatial L² envelope `g`
for the **signed** classical Navier–Stokes momentum (only where the test
coordinate is nonzero), uniform for nearby times and outside a single spatial
null set. No spatial Lipschitz modulus or spatial pointwise supremum is needed.

Because a compact smooth spatial test coordinate `φ_i` belongs to L², Hölder
2–2–1 proves the integrability of `‖φ_i(x)‖ ‖g(x)‖`. The pointwise classical
PDE identity supplies the domination of `φ_i ∂ₜu_i` by that product. Thus the
existing dominated parametric-integral derivative theorem gives weak FTC,
which the previous interior-time bridge promotes to the strong physical
Hilbert derivative and the actual regular time-distribution equation.

### Important boundary

An L² envelope (one *function* `g(x)` in L² dominating all nearby slices)
is stronger than merely knowing `sup_t ‖F(t,·)‖_{L²} < ∞`. Uniform norm
bounds alone do not provide a pointwise dominating function. Neither this
envelope nor the ensuing distributional equation is claimed to follow from
bare H³ path admissibility. The remaining genuine math is to derive the
required space-time control (perhaps by an alternate Bochner/Vitali/Fubini
argument), without introducing it as an axiom.

Declarations: `h3Path_compactTestL2Envelope_productIntegrable244`,
`h3PreterminalSignedMomentumLocalL2EnvelopeOnElapsed244`,
`h3Preterminal_compactTemporalDomination_of_signedL2Envelope244`,
`h3PathInteriorTimeSignedL2EnvelopeAt244`,
`h3Path_interiorTemporalDomination_of_signedL2Envelope244`,
`h3Path_physicalHilbertHasDerivAt_of_signedL2Envelope244`,
`h3Path_distributionalMomentum_of_signedL2Envelope244`, and
`h3Path_nonzeroPhysicalFTCDefect_forces_signedL2EnvelopeFailure244`.
