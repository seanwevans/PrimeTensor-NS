# Native signed sixth-flux: linear high-tail annulus and in-gap persistence

**Pinned base:** `00552eb99d3ce40efe4ca91e6a8a54937f57cffa` — gamma-free instantaneous physical H3 viscous gate.

## New mathematical step

The old theorem gives a strict-time high-radial alternative, but concludes only an instantaneous full H3 dissipation spike. On an actual adverse third-order physical sample `t`, its stronger pre-coercivity tail fact is

`eta/2 <= A(t) * ||P_R U(t)||^2`, where

`A(t)=((2*pi)^7/3)*1944*C1*(velocityH3EnergyAt(u,t)+1)`.

The **existing** genuine physical high-radial coercivity states

`(R+1)^2 * ||P_R U(t)||^2 <= D_high((R+1),U(t))`.

Consequently, with `Q=(R+1)^2*(eta/2)>0`, `Q<=A(t)*D_high`. Since `eta>0`, the tail inequality itself forces `A(t)>0`. Choose the new explicit strictly positive *linear-margin* height

`H_linear(R,eta,t) = Q / [2*(A(t)+1)]`.

Then `A(t)*H_linear < Q <= A(t)*D_high`, so `H_linear < D_high` at the **same actual physical time**. This avoids the previous squared-margin and squared-recovery-amplitude denominator. The height is a real physical energy/radial quantity; there is no Schwartz approximation and no arbitrary positive Fourier tolerance.

## Exact physical interval rather than a point spike

The accepted `thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244` converts that high-radial floor into a finite-annulus PDE-certified **positive-width** window. Two already proved results localize it to the original gap `[x,y]`:

- If `t<y`, `thirdFullPhysical_signedLowMax_certifiedWindow_truncateInGap244` retains positive forward width and `thirdFullPhysical_signedLowMax_inGapCharge_le_fullGapDissipation244` charges the actual full-H3 dissipation of `[x,y]`.
- If `t=y`, `thirdFullPhysical_signedLowMax_rightEndpoint_backwardGapCharge244` uses the true kinetic-only two-sided annular Lipschitz rate to propagate the same certified annulus backward within `[x,y]`.

Both cases yield a width `w>0`, with a certified forward or backward subinterval of `[x,y]`, and

`w * H_linear(R,eta,t)/4 <= integral_[x,y] D3(r) dr`.

No time-uniform full-dissipation continuity, hypothetical two-snapshot flux jump, or positive uniform width is used.

## Three-way cofinal physical obstruction

The preceding cofinal theorem establishes its alternatives for **every** positive gamma with a gap index uniform in gamma, cutoff and selected adverse time. Apply the accepted scalar gamma->0 lemma with the other physical alternatives independent of gamma. In the resulting high-tail branch, the new linear-in-margin interval theorem supplies the integrated charge.

The older signed-reference viscous branch already supplies an integrated gap charge with physical height

`H_quad(R,U(t),U(x),eta) = thirdFullKineticSignedLowMaxPhysicalViscousHeight244(R,U(t),U(x),mu/2)`

where `mu=(eta/2)/((2*pi)^7/3)>0`. Set `H_min=min(H_linear,H_quad)`, which is strictly positive at every physical strict time. Both integrated branches imply the same charge using `H_min`.

By the already-proved `thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244`, the full dissipation on the original separated cofinal gaps goes to zero. Thus, for every fixed radial cap `J`, physical energy cap `E` and epsilon>0, at all sufficiently late original gaps every adverse physical sample at **any radius** pays one of only three genuine physical alternatives:

1. Earlier physical signed LowMax cubic baseline at the actual left endpoint;
2. The cutoff exceeds `J`, or actual physical H3 energy at the adverse sample or at the left endpoint exceeds `E`;
3. A positive-width, forward/backward **in-gap** actual physical annular viscous charge `w*H_min/4 < epsilon`.

The integrated signed surplus variant selects the adverse time automatically from the original Navier–Stokes signed energy law when the prescribed excess condition holds.

## Limits

The theorem is a quantified necessary condition, not a Navier–Stokes continuation proof. The new **linear** floor is sharper than the squared-margin budget as an individual carrier but may go to zero with moving physical energy, cutoff and terminal time. Neither the minimum of the two certified positive heights nor its positive width has a cofinal-uniform lower bound. The left-endpoint signed baseline and radial/energy escape are not ruled out. The signed surplus is not asserted on every gap.

## Verification

The registrar inserts four definitions/predicates and five theorem checks. Regenerate `proof/generate_index.py` and run targeted `lake env lean`, Lake builds and complete audit under the pinned Lean toolchain before committing. Static checks below do not establish Lean kernel verification.
