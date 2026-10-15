# Critical-half and terminal-endpoint frontier correction (2026-10-15)

**Base:** `92a8cdcd` — `prove sharp five-order physical Schwartz interpolation`.
**Scope:** mathematical novelty and conditional-hypothesis audit. No Lean theorem or axiom is added or changed by this documentation checkpoint.

## 1. What the Lean development actually establishes

The physical real-Schwartz derivative energies `E0`, `E1`, `E2`, `E3` and the 243-slot fourth-order dissipation `D` have exact adjacent coefficient-one inequalities

    E1^2 <= E0*E2;  E2^2 <= E1*E3;  E3^2 <= E2*D.

The five-order specialization additionally proves

    E1^4 <= E0^3*D;  E2^2 <= E0*D;  E3^4 <= E0*D^3.

The signed 243-slot physical first monomial `M`, its amplitude and spatial scaling laws, the positive-endpoint balancing and unit-orbit representatives, and the invariant shape ratio are separately formalized. With `E0=E3=1`, `E1<=1`, `E2<=1` and `D>=1`. These are exact Schwartz facts; none alone bounds the nonlinear cubic `M`.

Relevant sources:

- `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadAggregate.lean`
- `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzFiveOrderInterpolation.lean`
- `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzUnitShapeReduction.lean`

## 2. The universal critical-half *inequality* is standard mathematics

The actual complex Schwartz first-monomial slot is a spatial integral of three factors with derivative orders `(3,2,2)`. Its real physical counterpart differs only by the known finite aggregate and real/complex identification. For any real Schwartz three-component field (no divergence-free assumption), finite summation and Hölder give

    |M(u)| <= C0 ||u||_{dot H^3} ||nabla^2 u||_{L^4}^2.

The homogeneous Sobolev embedding in three dimensions gives

    ||nabla^2 u||_{L^4} <= C1 ||u||_{dot H^(11/4)}.

Interpolation between `dot H^(1/2)` and `dot H^4` gives

    ||u||_{dot H^3} <= ||u||_{dot H^(1/2)}^(2/7) * ||u||_{dot H^4}^(5/7)
    ||u||_{dot H^(11/4)} <= ||u||_{dot H^(1/2)}^(5/14) * ||u||_{dot H^4}^(9/14).

Thus the low-norm exponents sum to `2/7 + 2*(5/14) = 1`, and the top-norm exponents sum to `5/7 + 2*(9/14) = 2`. As the complete ordered fourth-derivative energy is `D(u) = ||u||_{dot H^4}^2` in the corresponding derivative/Fourier normalization, it follows that

    |M(u)| <= C2 ||u||_{dot H^(1/2)} D(u).

Finally, Fourier Cauchy and the arithmetic-geometric mean yield

    ||u||_{dot H^(1/2)}^2 <= ||u||_2 ||u||_{dot H^1}
                                    <= (E0(u)+E1(u))/2,

hence for a fixed finite constant `C_*`

    |M(u)| <= C_* sqrt(1 + E0(u)+E1(u)+E2(u)+E3(u)) D(u).

This is an **existing analytic implication**, not yet a Lean theorem about the project's precise `SchwartzMap`, `LineDeriv`, measure, and normalization definitions. The constants depend on normalization of Sobolev norms and the finite coordinate sum, not on `u`.

Consequences:

- A finite universal critical-half coefficient **does exist mathematically** for all Schwartz profiles, not just solenoidal ones.
- The shape ratio `R = M^12/(D^12 E0^5 E3)` is therefore uniformly bounded on positive-endpoint Schwartz fields: normalize to `E0=E3=1`, use `E1<=1`, and transport the bound by the proved orbit invariances.
- Conditional positive balanced excess may refute a **particular too-small** proposed coefficient. It cannot refute every finite coefficient by a family of profiles.
- The proved obstruction to an exponent `theta < 1/2` is a genuine sharpness fact from cubic-versus-quadratic amplitude homogeneity, not evidence that the endpoint `theta=1/2` fails.

The formal proof of the *known* bound should be a bounded Lean task: prove a physical Schwartz `L^4` Sobolev estimate for actual second derivatives, interpolate fractional homogeneous norms, assemble the 243 signed slots with a concrete finite constant, and connect those norms with the exact `E` and `D` definitions.

## 3. The bound alone does not close Navier--Stokes regularity

An H3 energy identity can contain a term of schematic size

    C_* ||u(t)||_{dot H^(1/2)} D(t).

Absorption into viscosity works only when this coefficient is sufficiently small, or after some *additional* integrable control or sign/cancellation estimate. The standard bound by itself does not provide global-in-time smallness. Any claimed unforced large-data regularity mechanism must exploit genuine additional structure of the true Navier--Stokes nonlinearity, beyond generic Holder/Sobolev/interpolation estimates. Compare Tao's averaged-model blowup example: https://arxiv.org/abs/1402.0290.

**Research acceptance test:** state the new dynamical estimate explicitly, prove its hypotheses from the real PDE rather than assuming a terminal bound, and show what fails for a generic averaged bilinear operator.

## 4. Strong H3 terminal endpoints: serious known-criterion redundancy

`H3TerminalActualVorticityStrongH3EndpointPath hH3 i` is misleadingly named if read as a weak endpoint for one vorticity coordinate: it supplies **strong weighted spectral H3 endpoint control for two transverse physical velocity components**. The repository's own `OneComponentEndpointBound` and `OneComponentIntrinsicSobolevTimeL2` files derive uniform late-time H3 control and a genuine physical `L^2_t dot H^(3/2)_x` quantity for a selected component on positive-start terminal intervals.

Liu and Zhang, *On the One Time-Varying Component Regularity Criteria for 3-D Navier-Stokes Equations*, SIAM J. Math. Anal. 56 (2024), 6213–6231, https://doi.org/10.1137/23M1623124, give a continuation criterion for one admissible velocity component in `L^2(0,T; dot H^(3/2))` for the appropriate local-strong-solution class. Constant coordinate directions are included. Applying the published result on a **time-shifted positive-start** interval may avoid proving an unnecessary initial-time H3 trace.

This is strong evidence that the historical `hPhysical` nonextension branch is empty **for a compatible local strong Navier--Stokes solution**. It is not yet a Lean theorem: the paper's exact solution class, Sobolev convention, interval translation, and continuation/restart conclusion must be bridged faithfully to the repository interfaces. `H3AuditOnePhysicalEndpointLiteratureBridge` remains an explicit *unproved* proposition. These strong endpoint hypotheses are not known for every H3 path and therefore cannot be used to claim global regularity.

## 5. Tail tightness is a conditional criterion, not new PDE compactness

Uniform high-frequency tightness of the top-order dissipation tail is a legitimate conditional continuation hypothesis in the present project. Its negation implies cofinal escape by elementary selection; radial coercive-weight bounds imply tightness through standard mass-tail estimates. These logical reductions do not supply the missing bound from Navier--Stokes dynamics.

Moreover frequency-tail tightness alone is not literally precompactness of a whole trajectory in spatial `L^2(R^3)`, because spatial translations can defeat compactness while preserving Fourier magnitudes. Avoid equating the two without spatial tightness or a suitable quotient.

The README should therefore describe *conditional terminal spectral-tail criteria*, not a solved or newly reduced global-regularity frontier.

## 6. Concrete next steps

1. Formalize the already-known Schwartz critical-half `L^4` / fractional interpolation inequality with an honest, explicit coefficient; remove claims that existence of any uniform constant is mathematically open.
2. In parallel, check the `hPhysical` endpoint interface against the published one-component theorem, preferably on a shifted interval, without introducing a paper-shaped axiom.
3. For genuinely new hard mathematics, isolate a *true-NS-only* signed cancellation or a priori dynamic estimate strong enough to beat the critical coefficient at arbitrary amplitude. Keep necessary terminal alternatives as conditional infrastructure.

No result here claims to prove or disprove unforced 3D Navier--Stokes global regularity, nor does it change the algebraic `PrimeTensor.Depth` foundation or the logarithmic bridge.
