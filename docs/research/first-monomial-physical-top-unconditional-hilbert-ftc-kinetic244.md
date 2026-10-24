# Unconditional all-positive-time physical Hilbert FTC and kinetic rate (244)

Baseline: `1d9b398d` (close physical momentum distributions from old pressure joint continuity).

The preceding physical momentum result proves `HasDerivAt U (R t) t` on every strict physical time from `LoggedPreterminalH3PathAdmissible` without separately assumed old temporal-derivative joint continuity. The already compiled `OneComponentInitialPhysicalHilbertGlobalFTC` proves the Bochner integrability of the same exact R between any pair of strictly positive times (even reversed), but its older global evolution theorem retains a conditional old-joint-continuity argument. This new module removes that premise by replacing its derivative invocation with the unconditional strong derivative.

Results:

* Physical Hilbert FTC, all positive-time endpoint orders: `U(t)-U(s)=∫_s^t R(r) dr`.
* Anchor-independent Bochner evolution `U(t)=U(s)+∫_s^t R`.
* Vanishing of the exact projected FTC defect even for reversed positive endpoints.
* `DifferentiableOn ℝ U (Ioo 0 T)` and exact derivative `deriv U=R` on the open interval.
* Strong continuity of the actual Hilbert derivative on `(0,T)`.
* Differentiation against every fixed physical L² probe, not just compact solenoidal tests.
* Physical L² kinetic differential identity `d/dt‖U‖² = 2⟪U,R⟫`.

Dependency audit: `h3Path_physicalHilbertHasDerivAt_fromH3Admissible244` uses global old-pressure joint continuity, which itself uses the previously proved curl weak-FTC / selected physical evolution branch. Hence the new result strengthens the physical *interface* and does not constitute an independent evolution proof or solve endpoint regularity/global Navier–Stokes.

Potential remaining work: combine the L² kinetic rate with physical H³ signed transport/dissipation, and examine whether the signed 244 channel obstruction can be excluded rather than only quantified. No initial or terminal endpoint conclusion is claimed.
