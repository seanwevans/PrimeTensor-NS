# Actual physical PDE rate on the residual two-clock H3 action

**Base:** `c69e603bc2e398ec7dffd6857babbfd3b1e56d99` — exact overlap envelope on the prescribed-gauge cofinal sequence.

## Quantitative result

For the existing actual primary clock `[r,r+eta1]` with full-H3 dissipation floor `A`, the actual secondary clock `[s,s+eta2]` with floor `H = h/2`, and physical terminal action `B = integral_m^T D_H3`, set

    L = min eta2 (max 0 (s+eta2-(r+eta1)))
    E = B - eta1*A - L*A.

The exact envelope implies, whenever `A <= H`,

    0 <= E,
    eta2*(H-A) <= E.

The ACTUAL projected Navier--Stokes finite-band PDE time clock fixes

    eta2 = min ((T-s)/4) (H/(2*(Lambda2+1)))
    Lambda2 = thirdFullLateViscousLowRadialPDERate244 J2 K2 C2
    K2 = ||actual weighted Fourier velocity(zState)||
    C2 = ||actual projected momentum source(zSource)||.

Therefore either

    (T-s)*(H-A) <= 4*E

or

    H*(H-A) <= 2*(Lambda2+1)*E
             <= (48*K2*C2*(J2+2)^5+2)*E.

The factor 24 in the polynomial majorant is the existing physical PDE estimate, not a new assumption. This formalizes the late source/state/frequency-rate obstruction **after deducting the dissipation already certified by the first clock**.

## Scope

The selected-clock physical theorem proves the rate trilemma from a matching exact envelope. The stronger `thirdFullPhysical_dualSelectedClock_residualPDERate244` **constructs** that matching envelope from both actual PDE-clock certificates, destructing the secondary clock only once and retaining its very same `s`, `eta2`, `J2`, `zState`, and `zSource`. Thus no independent overlap-envelope assumption is needed on actual dual clocks. The scalar activation lemma shows `24 sqrt(R B) < 1` and `A > 0` imply strict secondary excess `A < A/(24 sqrt(R B))`. No uniform bound on the selected physical maxima is assumed. The previous cofinal exact-envelope proposition does not retain `J2` and the attained secondary PDE maxima, so a subsequent cofinal lift must preserve that exact certificate rather than inferring it from a separately selected existential witness.

No terminal regularity or unconditional non-kinetic gap is claimed. The existing no-H3-trace cofinal exact-envelope theorem does not yet retain the new secondary `J2` and attained maxima; a next cofinal transfer must preserve this same certificate to apply the new PDE-rate gate. The patch contains no proof placeholders. Full Lean elaboration must run with the repository's pinned Lean/mathlib toolchain.
