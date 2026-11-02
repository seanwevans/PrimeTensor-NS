# Disjoint physical H3 annuli: energy, source and outer-frequency barrier

**Base:** `62cd7abc` (`transfer quarter-cubic H3 annular gap to physical sixth and ninth PDE barriers`).

## Mathematical statement

Under `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and
failure of the physical terminal L2 velocity trace, the cofinal exact-anchor
quarter-gap annuli are selected with their original nonoverlapping physical
intervals, positive cubic annular charge, and exact sharp quadratic PDE width.
The newly exported per-window data include

* inner radius `R_k = v(k)+1`, outer radius `Q_k = N(v(k))+1` and `R_k <= Q_k`;
* attained projected-source envelope `C_k` on the terminal half-window;
* anchor `K_k = ‖h3AuditActualSpectralVelocityTotal hH3 (t(v(k)))‖`, with
  `K_k² <= velocityH3EnergyAt u (t(v(k)))`;
* strict quarter-cubic surplus and local annular integral cost.

One of the following holds:

1. The finite partial sums of certified nonnegative charges
   `delta(v(k)) * R_k³/2` are unbounded.
2. For every `epsilon > 0`, sufficiently late indices obey at least one:

   * `R_k³ (T - t(v(k)))/4 <= epsilon` (terminal compression);
   * `R_k^12 <= 512 epsilon² (2304 E3(t(v(k))) C_k² (Q_k+1)^10 + 1)`;
   * `R_k^9 <= 16 epsilon² (36 C_k² ((Q_k+1)^8+(R_k+1)^8) + 1)`.

The scalar implication reuses the prior checked H3 energy-source rate-square
and eighth-power quadratic frequency bounds. This introduces no independent
source supremum, frequency cap, positive terminal kinetic-mass hypothesis, or
finite terminal full H3 dissipation. It does not show that the charge sums
diverge, exclude the PDE coefficient branches, or establish continuation.

## Lean declarations

* `h3Critical_scalar_quarterCubicRates_to_energySourceOuter`
* `h3Critical_noL2Trace_disjointQuarterCubicAnnuli_energySourceOuterBarrier`

## Verification

Run the registrar `--apply` and `--check`, generate and check the proof index,
then compile the module, build the full project, and run the established audit.
The Lean compiler is unavailable in the patch-construction environment.
