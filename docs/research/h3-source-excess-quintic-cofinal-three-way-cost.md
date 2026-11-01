# Cofinal quintic source peaks: physical three-way concentration obstruction

Base `d9f9acd8`: the accepted one-window quintic physical dissipation gate.

## New genuinely physical rate split

Write `κ=3(3+C_L)>0`, `S=max(1,σ)+1`, and
`Y=A²B`, with the actual PDE source/spectral/viscous cost coefficients
from the fivefold source-peak physical theorem. If the original source
window width `w` and an actual local physical dissipation charge `J>0`
obey the accepted alternative

    w <= J/(M+q/κ)  OR  64 q⁵ <= κ J (16 S² q² + Y)²,

then using `(X+Y)² <= 2(X²+Y²)` gives an unavoidable **three-way** branch:

    (1) w <= J/(M+q/κ), or
    (2) q <= 16 κ J S⁴, or
    (3) 16 q⁵ <= κ J (A²B)².

Branch (1) is geometric source-window compression. Branch (2) requires
cutoff frequency S⁴ to be large enough relative to the prescribed source
margin q and the actual charge J. Branch (3) requires growth of the local
actual PDE cost A²B sufficient to absorb the quintic source-margin charge.
There is no presumption that the third branch contradicts an energy identity.

If the original window is noncompressed and `q > 16κJS⁴`, the actual local
PDE cost MUST pay `16q⁵ <= κJ(A²B)²`. This is independent of any Fourier
radius chosen by the proof. It is also stronger information than simply
repeating the quintic inequality.

## Cofinal transfer

Under the existing no-physical-L²-terminal-trace branch, choose the
source-excess profile `5q(n)` in the accepted *full-window separated*
source-driven theorem. For each source peak, obtain compact strict-time
source and spectral-state ceilings from actual continuity, and apply the
accepted single-peak fivefold quintic charge theorem. This yields one
Fourier coordinate, cofinal times, disjoint calibrated subwindows, their
explicit source-dependent lower widths, actual full physical H³
pointwise floors, and extended Lebesgue height-times-width lower costs.

Crucially the three-way cost alternative is attached to the SAME interval
and its actual physical integral. The local `J` may depend arbitrarily on
the index; no terminal-uniform bound or global finiteness is imported.

The analytic frontier is now whether actual NS energy/transport bounds
can exclude the PDE-cost growth branch while geometrical windows and
cutoff radii are controlled. No terminal contradiction or unconditional
Navier–Stokes regularity is claimed.

## Lean declarations

- `h3Critical_quinticMargin_cutoffOrPDECost`
- `h3Critical_quinticCutoffBranch_normalizesToLinearSource`
- `h3Critical_quinticMargin_normalizedCutoffOrPDECost`
- `h3Critical_quinticMargin_largeSource_forces_PDECost`
- `h3Critical_noL2Trace_cofinalFivefoldSource_quinticThreeWayCostGate`

Static audit and ZIP verification do not substitute for elaboration in
PrimeTensor-NS's pinned Lean/mathlib environment.

## Lean elaboration correction (fix1 at `d9f9acd8`)

The former `mul_le_mul_left hFactor` application incorrectly used `.mp`
although this lemma is a forward monotonicity statement, not an equivalence.
To cancel the strictly positive factor `16*q^4`, the corrected proof assumes
the desired inequality fails, multiplies the strict reverse inequality by
the positive factor with `mul_lt_mul_of_pos_left`, and contradicts `hRest`.
The unused existential `Fin 3` binder is renamed `_i` to suppress the
unused-variable warning. The theorem proposition and hypotheses are unchanged.
