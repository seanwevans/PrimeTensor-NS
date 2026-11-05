# Quantitative terminal H³ high-radial viscous escape

Baseline: `487922ec2f056a92639afacbbde6d5d43f51437d`.

The latest terminal radial compactness criterion for the *actual* H³
spectral velocity identifies a failure of strong H³ convergence with
endpoint-cofinal high-radial square-mass escape of one fixed positive size.
This patch connects that genuinely weighted Fourier velocity norm to the
actual physical H³ dissipation, avoiding any identification of a sup norm
with the three-component Fourier square energy.

## Exact projection and physical dissipation

The high-pass scalar operator is the exact sharp indicator of the complement
of the natural Fourier gradient ball of radius `rho = R+1`. The new first
module proves, for any spectral velocity state `U`, the exact identity

    h3SpectralVelocitySquareEnergy (P_R U)
      = h3PathActualSpectralHighRadialRemainder244 (R+1) U.

For the finite product with a sup norm, only the inequality

    ||P_R U||^2 <= h3PathActualSpectralHighRadialRemainder244 (R+1) U

is asserted. It is combined with the repository's exact coercivity theorem
`h3Path_actualHighRadialDissipation_ge_squareHighMass244` and existing
full-dissipation comparison `h3Path_highRadialMass_le_fullDissipationAt244`:

    (R+1)^2 ||P_R U(t)||^2
      <= HighH3Dissipation(R+1,U(t))
      <= FullPhysicalH3Dissipation(t).

No new integral estimates or unverified norm identities are introduced.

## Terminal diagonal escape

Assume a `LoggedPreterminalH3PathAdmissible` trajectory with a
`PreterminalH3EnergyClass` and **failure of the strong terminal H³ spectral
trace**. Existing `thirdFullPhysical_noH3Trace_iff_cofinalHighRadialEscape244`
provides one `epsilon > 0` that works for all natural cutoff radii and all
terminal windows.

At radius `R=n` and terminal width `1/(n+1)`, choose `tau_n` with

    tau_n < T,  T-tau_n < 1/(n+1),  ||P_n U(tau_n)|| >= epsilon.

Then `tau_n -> T` and, **at the same selected times**, both high-radial
H³ dissipation and full physical H³ dissipation satisfy

    Dissipation(tau_n) >= epsilon^2 (n+1)^2.

The genuine high-radial H³ dissipation is antitone in its cutoff radius. Thus,
for *every fixed real cutoff sigma*, the high-radial dissipation at `sigma`
diverges along this exact `tau_n` sequence. This is stronger than obtaining
separate unrelated spike times for each sigma.

The derived corollary is that a terminal tail with a uniform bound on full
H³ dissipation has a strong H³ spectral trace. By contrast, the patch does
**not** prove bounded dissipation or endpoint-uniform high-radial tightness.

## Sharp remaining frontier

The pointwise quadratic viscous spike lower bound does **not** imply a
nonintegrable full H³ dissipation near `T`. To promote these spikes to a
contradiction with the available endpoint energy budget would require a
quantitative lower bound on their time widths or a summable disjoint charge.
The earlier finite-annular persistence machinery is a natural place to
seek such a width estimate; that estimate is not silently assumed here.

## New modules

1. `FullThirdSolenoidalHighRadialViscousCoercivity.lean` — projection square
   energy and genuine physical viscous coercivity.
2. `FullThirdSolenoidalTerminalViscousEscapeDiagonal.lean` — one terminal
   quadratic-cost sequence, all-fixed-radius dissipation divergence, cofinal
   spikes, and bounded-dissipation endpoint criterion.

Run `tools/audit/register_h3_full_third_solenoidal_terminal_viscous_escape_diagonal.py`
with `--apply` and `--check` before `proof/generate_index.py` and the full audit.

## Lean proof repair (fix 1)

The scalar-integrand case split now uses the literal `h3TopTailNaturalHighRadialSet R` rather than the local abbreviation `S`. This makes `Set.indicator_of_mem` and `Set.indicator_of_notMem` match the Fourier representatives before unfolding the pointwise spectral amplitude. No theorem statement or estimate changes.
