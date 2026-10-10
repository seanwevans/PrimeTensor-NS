# One-component endpoint bridge: first proved analytic step

Baseline: `d776eb85` (frontier boundary audit). This is a review of the exact
Lean hypotheses and the Liu–Zhang one-velocity-component continuation theorem.
It does not claim the outside theorem has been formalized or that Navier–Stokes
regularity has been proved unconditionally.

## Exact published comparison

Yanlin Liu and Ping Zhang, *On the One Time-Varying Component Regularity
Criteria for 3-D Navier–Stokes Equations*, SIAM J. Math. Anal. 56 (2024),
6213–6231, DOI 10.1137/23M1623124:
https://doi.org/10.1137/23M1623124

For a local strong solution of three-dimensional incompressible Navier–Stokes,
their result gives continuation when one velocity projection `u(t)·β(t)`
obeys `∫₀ᵀ ‖u(t)·β(t)‖_{Ḣ^{3/2}}² dt < ∞`, with β(t) an admissible piecewise
H¹ unit vector. A fixed coordinate axis is an admissible choice.

The repository's `H3TerminalActualVorticityStrongH3EndpointPath hH3 i`
requires strong weighted spectral H³ endpoints for the TWO velocity
components transverse to i. Under the usual Fourier/Sobolev correspondence,
this is considerably stronger than the spatial Sobolev regularity required
by the published one-component criterion, on a terminal time interval.

## What this checkpoint actually proves

`H3/Audit/OneComponentEndpointBound.lean` proves three statements:

1. A pathwise strong endpoint for one complementary velocity coordinate
   implies a uniform finite weighted spectral H³ norm bound near T.
2. A single physical `hPhysical` supplies one terminal window and one finite
   bound for BOTH complementary velocity coordinates.
3. Their squared spectral norms have a single finite upper budget on that
   window.

All three are unconditional deductions from the named endpoint predicate;
none assumes the literature-transfer proposition.

## Remaining *precise* proof obligations

* Identify each repository `H3SpectralScalarState` at a strict time with the
  physical Fourier transform of the corresponding real velocity component,
  and establish the estimate `‖u_j(t)‖_{Ḣ^{3/2}} ≤ C‖G_j(t)‖_{H³-weighted}`.
  In Fourier variables, this follows from the elementary weight comparison
  `|ξ|³ ≤ 1+|ξ|²+|ξ|⁴+|ξ|⁶`; its formal connection to the actual velocity
  and measures requires an explicit proof.
* Prove time measurability and integrability of the homogeneous Sobolev norm
  on a late finite time interval, using the boundedness theorem above.
  The interval away from the terminal time needs the strict-time strong
  solution regularity already encoded by the path class.
* Establish that the Lean `LoggedPreterminalH3PathAdmissible` plus the PDE
  witness in `PreterminalH3EnergyClass` corresponds to the publication's
  **local strong solution** of the genuine 3-D incompressible equations.
* Translate the publication's continuation conclusion to the project's
  `SmoothContinuationExtension` or, preferably, a genuine real restart.
  Citing a paper is not a Lean proof of this mapping.

## Implication for the endpoint branch

Once these obligations are established, the proposition
`H3AuditOnePhysicalEndpointLiteratureBridge` from `Audit/FrontierBoundary.lean`
can be proved rather than postulated. The nonextension branch of the endpoint
alternative, *under its present `hPhysical` hypothesis*, would then be empty
by known mathematics. That would be a valuable formalization and redundancy
audit, not a new Navier–Stokes regularity theorem.

## Scope and strategic boundary

This project already proves path-specific restart from `TerminalTailH3Control`.
It does NOT prove that all admissible paths satisfy that terminal bound. The
separate arbitrary-initial-data / maximal-interval / global-existence bridge
for Clay Form A remains unformalized. Do not infer that global regularity
follows from component endpoint hypotheses, since those hypotheses are not
known to hold universally.
