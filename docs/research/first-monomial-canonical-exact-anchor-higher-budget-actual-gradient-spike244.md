# Physical pointwise velocity-gradient spikes from critical H³ annular logarithmic radii

Base: `e8e85187` — charge critical H3 logarithmic radius and viscosity to physical gradient.

## New target: actual first spatial derivatives, not a C¹ majorant

The committed canonical signed logarithmic radius gate provides the conditional lower bound, for all sufficiently large canonical indices k, at a genuine intermediate physical time s in (b, τ(v k)):

    p log R_k <= log C_b + 4(T-b) g(s),
    p=16m+3, R_k=v(k)+1,
    g(s)=max(0,(-Transport₃(s)-2D₃(s))/E₃(s)).

Unlike the earlier bound involving the *canonical* gradient upper envelope, this module addresses a real pointwise spatial derivative. The complete H³ commutator theorem is formulated for any function `h` giving `VelocityGradientEnvelope u h s`. At a selected single time s we splice an arbitrary bound H into the already-proved square-root-H³ energy gradient envelope at all other times. The transport closure remains valid because its assumptions are pointwise in time and do not require continuity of the envelope. Therefore:

    VelocityGradientEnvelope u (fun _ => H) s
      ==> g(s) <= 4422 (1+|H|).

If `g(s)>0`, the full viscous expenditure can also be retained:

    g(s) + 2 D₃(s)/E₃(s) <= 4422 (1+|H|).

## Sharp conditional actual-gradient consequence

Fix any `c >= 0` satisfying

    4(T-b) * 4422 * c < 16m+3.

For every sufficiently late k, the unhalved logarithmic radius budget supplies a time `s` in `(b, τ(v k))` at which some **actual** coordinate first derivative and spatial location `(i,j,x)` satisfy

    c log(v(k)+1) < |∂ᵢ uⱼ(s,x)|.

Proof by contradiction: if every actual derivative at that same s were at most `c log R_k`, the one-time gradient-envelope commutator would give

    g(s) <= 4422 (1 + c log R_k).

Combining with the sharp radius gate yields

    (p - 4(T-b)4422 c) log R_k <= log C_b + 4(T-b)4422.

The left side tends to infinity because the coefficient is positive and `v` is strictly increasing; the right side is fixed. Therefore a real derivative must exceed the threshold at the selected s. No optimization over actual gradient suprema, spatial maximizers, or measurability of a supremum is assumed.

This is a stronger physical conclusion than growth of the canonical gradient **upper** envelope, but still wholly conditional on the original higher-radial moment majorant, projected source ceiling, critical outer-cutoff, small epsilon, and weighted noncompressed terminal clock. No unconditional Navier–Stokes singularity or regularity conclusion is claimed.

Declarations:

- `h3Path_fullSignedExcess_le_arbitraryOneTimeActualGradientBound244`
- `h3Path_positiveFullExcess_add_viscousShare_le_actualGradientBound244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientLogSpikes244`

Full Lean compilation requires the repository-pinned Lake toolchain. Offline structural validation is not a Lean proof check.
