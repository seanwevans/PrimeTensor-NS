# Selected outer carrier: necessary physical temporal-rate amplification

Local prerequisite: `0b9ff75c1` (`FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierExplicitTemporalRate`). The GitHub remote had not yet exposed that commit when this continuation was prepared; install on the user's local HEAD after checking that prefix. This package does not replace the preceding file.

## The quantitative obstruction

Fix selected physical snapshots `x_k -> T`, actual highpass kinetic excess margins `m_k > 0`, actual annular Young-width deficits with positive floors `2 epsilon_k > 0`, and outer radii `sigma_k >= 2 rho_k > 0`.

The exact physical H3 viscous-spike result is `119 m sigma^6 <= 80 D_H3` wherever the margin and deficit signs persist. The previous module assumed forward Lipschitz rates `LM` for the **weighted actual kinetic highpass** and `LG` for the **actual annular kinetic deficit**, and obtained the rigorous cost

    min { m/(2 LM), epsilon/LG, (T-x)/2 }
      * (119 m sigma^6/160) <= V(x),
    V(x) := integral_x^T D_H3(t) dt.

Unlike an arbitrary continuity window, this minimum can be eliminated exactly. Every selected snapshot satisfies at least one of

    119 m^2 sigma^6 <= 320 LM V(x)                    (mass-rate arm)
    119 m epsilon sigma^6 <= 160 LG V(x)             (deficit-rate arm)
    119 m sigma^6 (T-x) <= 320 V(x)                 (time-compression arm).

No artificial lower bound on the time window is introduced. No division by `V` is required; the inequalities remain meaningful when the viscous tail vanishes.

Now assume the **non-collapsing scaled time distance**

    eventually 0 < c <= m_k sigma_k^6 (T - x_k).

Because finite physical H3 dissipation gives `V(x_k) -> 0`, the time-compression arm is eventually impossible. The other arms yield the stronger necessary amplification:

    for every C>0, eventually
       LM_k > C m_k^2 sigma_k^6
       OR
       LG_k > C m_k epsilon_k sigma_k^6.

The disjunction can alternate with k. This does **not** prove either rate individually tends to infinity, nor assert that the non-collapsing scaled time-distance hypothesis follows from the PDE. Both distinctions matter.

## Resolving the exact deficit rate into two physical observables

The exact kinetic deficit is the polynomial

    G(m,y) = w (a m - b)^2 - m (y + w p),

where `m` is actual sharp highpass mass, `y` is the original nonlinear Young-width cost, and `a,b,w,p` are the same fixed physical coefficients as in the existing two-time ledger.

At times s and x, with physical highpass mass rate `lm`, actual Young-width rate `ly`, highpass bound `M`, and exact two-time slope bound `S`, the new theorem proves

    |G(s)-G(x)| <= (lm*S + M*ly)*(s-x).

This identifies the concrete deficit rate `LG = lm*S + M*ly`; no opaque derivative of G needs to be postulated. Both independent rates still require a PDE-based proof, and the existing finite-radius slope ceiling can be used in future work.

## Lean names

- `thirdFullKinetic_deficitPolynomial_rateFromTwoChannels244`
- `thirdFullPhysical_actualAnnularDeficit_rateFromTwoChannels244`
- `thirdFullKinetic_explicitOuterRate_threeWayBarrier244`
- `thirdFullKinetic_outerRate_threeWay_noTimeArm244`
- `thirdFullKinetic_outerRate_smallTail_amplification244`
- `thirdFullPhysical_cofinalSelectedOuterMargins_forceRateAmplification244`

The file contains no proof placeholders or introduced axioms. Local Lean compilation under the pinned project toolchain is still required.
