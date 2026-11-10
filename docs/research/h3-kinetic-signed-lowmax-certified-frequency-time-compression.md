# Signed LowMax: certified annular frequency–time compression

**Pinned HEAD:** `3359a46f305184ce0c71724c5e103ca1ae97afdd`.

## Mathematical advance

The accepted `...CertifiedEleventhFrequencyCharge` theorem proves a genuine
physical annular H³ dissipation peak at the SAME outer radius `Q` as its
symmetric persistence width `w` and its integrated original kinetic-gap
charge `D`. The peak is not an arbitrary natural-number cutoff.

Write `h > 0` for the capped linear physical-height floor, `H >= h` for
its actual selected high-radial physical-height bound, `L` for the
KINETIC annular endpoint rate, and

```
w = min ((y-x)/4) (H/(8*(L+1))),
w*(H/4) <= D,
16*D < (y-x)*h.
```

The last inequality excludes `w = (y-x)/4`, since it would imply
`(y-x)*H <= 16 D`. Therefore **the minimum selects the rate branch**:

```
w = H/(8*(L+1)).
```

The accepted one-annulus bound supplies

```
L+1 <= K(E0)*(Q+1)^11,
K(E0) = 1 + 192 sqrt(E0)*(sqrt(E0)+54 E0) > 0.
```

Consequently the SAME physical witness satisfies the two-sided
frequency–time concentration inequalities

```
h <= 8*K(E0)*(Q+1)^11*w,  and  w*h <= 4*D.
```

The first is a **minimum temporal persistence at a given certified outer
frequency**. The second is a **maximum persistence under a given actual
dissipation budget**. Their combination recovers the eleventh-power
charge `(Q+1)^11*D >= h^2/(32*K(E0))`, but separately they expose the
frequency–time mechanism responsible for that charge.

## Cofinal physical conclusion

On the original separated kinetic gaps, `D(k) -> 0`. For any fixed
outer-radius threshold `B` and positive width tolerance `zeta`, there is
a late gap threshold such that every qualifying adverse sixth-flux sample
(energy cap from the excluded tenth-power residual, and low relative
physical dissipation) admits one ACTUAL certified annular `Q > B` with
`0 < w < zeta`, its exact symmetric rate width, physical annular H³ peak,
original in-gap charge, and both frequency–time inequalities.

The eventual threshold may depend on `B` and `zeta`, but is uniform in
the selected adverse time `t` and inner natural cutoff `R`.

## Formal declarations

- `thirdFullKinetic_signedLowMax_lowDensity_forcesRateWidth244`
- `thirdFullKinetic_signedLowMax_certifiedWidth_twoSided244`
- `thirdFullKinetic_signedLowMax_gapDissipation_forcesWidthCollapse244`
- `thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyTimeCompression244`

## Scope and limitations

The theorem remains conditional on the true adverse physical sixth-flux
observation, exclusion of the accepted tenth-power residual, and low
relative gap dissipation. Neither finite dissipation alone nor the two-sided
inequalities rules out high-frequency concentration, constructs a terminal
H³ trace, or settles Navier–Stokes continuation.

Lean elaboration must be tested against the user's pinned Lean/mathlib.
