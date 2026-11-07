# Native solenoidal sixth-power Fourier flux on the genuine kinetic H³ gaps

**Base HEAD:** `309a6b3fdfd2305c4d3ec46dd279952d26c60688`.

## Why another cumulative scalar alternative is not sufficient

The accepted `FullThirdSolenoidalTerminalProfileKineticCumulativeSignedGapTransport`
proved an exact cofinal drain/positive-gap-transport budget on a single
sequence of genuine kinetic PDE persistence windows. Its positive gap
integral was still the unestimated physical full H³ signed transport surplus.
A small *raw* kinetic carrier or a vanishing unweighted source-L¹ action
cannot, without additional differentiated Fourier control, bound that integral.

## Physical native Fourier flux transfer

The existing `FullThirdSolenoidalMinimumFrequencyPartition` proves that the
*complete six-order complex solenoidal flux* has a measurable, disjoint
minimum-frequency partition and a global H³-weighted Schwartz bound:

    norm (integral F6) <= 1944*C1*K^3.

It also provides the genuine real-solenoidal Schwartz approximation of any
Fourier-compatible physical Navier–Stokes snapshot, converging to the actual
physical order-three signed transport (including the `(2*pi)^7/3` phase factor).
Here the approximation is bounded by the explicit physical kinetic-energy
quantity `K = E3(t) + 1`: its strong weighted Fourier convergence and the
accepted physical encoder bound `norm U <= E3(t)` imply the required
`norm (V_n) <= K` eventually. Pass the *absolute* flux inequality to the
physical limit, retaining the actual complex phase and all three sectors:

    abs(T3_top(t)) <= ((2*pi)^7/3)*1944*C1*(E3(t)+1)^3.

No snapshot-dependent existential constant or independent higher moment is
left in this inequality. It is an energy-cubic estimate, **not** an
endpoint-time uniform bound. The numerical constant is not claimed optimal.

## Signed physical surplus on a compact gap

The previously proved exact physical lower-order transport inequality is

    E3'(t)+2D3(t) <= 24*Cgrad*sqrt(E3(t))*E3(t)-T3_top(t).

The exact full H³ balance then bounds the positive signed replenishment

    max(0,-Transport3(t)-2D3(t))
      <= 24*Cgrad*sqrt(E3(t))*E3(t)
           + ((2*pi)^7/3)*1944*C1*(E3(t)+1)^3.

The full physical H³ energy is continuous on every strict preterminal
interval. Thus the right side is integrable on each **compact** physical
inter-window gap. Integrating it bounds the existing signed-gap-replenishment
term, not an unweighted Fourier L² substitute or a signed source maximum.

## Same-witness cumulative conclusion

Use the ORIGINAL `ThirdFullKineticNaturalAnnularLocalWitness244` windows
selected by the accepted cumulative theorem, with their exact cutoffs,
widths, cofinality, separation, global extended-viscous-charge packing,
vanishing absolute projected-source L¹ action and uniform moving raw Fourier
annular tightness. For each finite index `m`, either some unchanged window
has a real physical Riccati-scale energy observation, or

    sum_{k=0}^m delta_k*(M_k/4) + 1 <= E3(t_0)
       + sum_{k=0}^{m-1} integral_{gap_k} [
           24*Cgrad*sqrt(E3)*E3 + ((2*pi)^7/3)*1944*C1*(E3+1)^3
         ].

This is an actual native solenoidal Fourier bound on the nonlinear
replenishment mechanism on every gap. Its right side need **not** be finite
on the terminal half-open interval; neither global H³ continuation nor a
contradiction follows. The remaining hard step is an independent control of
that physical energy-cubic integral or a sharper radial/phase cancellation
that reduces the growth exponent in the concentration regime.

## Lean declarations

- `thirdFullPhysical_topThird_sixthFlux_le_energyCubic244`
- `thirdFullPhysical_positiveSignedSurplus_le_sixthFluxCubic244`
- `thirdFullPhysical_gap_positiveSurplusIntegral_le_sixthFluxCubic244`
- `thirdFullPhysical_kineticDisjoint_cumulativeSixthFluxGapBudget244`
- `thirdFullPhysical_noH3Trace_kineticSixthFluxGapObstruction244`

No new axioms, `sorry`, or `admit`; Lean elaboration must be verified in the
pinned toolchain. The local audit only checks syntax/registration of declarations.
