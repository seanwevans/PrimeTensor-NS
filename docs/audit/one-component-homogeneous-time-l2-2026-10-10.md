# Fourier homogeneous three-halves time-L² bridge (2026-10-10)

Base checkpoint: `c0f87410` (`globalize homogeneous H3/2 time measurability`).

The new file `OneComponentHomogeneousTimeL2.lean` defines the nonnegative
square root of the exact componentwise Fourier square density. The already
proved global measurability of the square density implies measurability
of the seminorm. Nonnegativity and `Real.sq_sqrt` make the time-L² criterion
exactly equivalent to integration of that square density on a strict tail.

Both transverse componentwise Fourier seminorms belong to the real-time
`MemLp ... 2` space on the SAME late interval under the already named
physical-curl endpoint and preterminal energy-class hypotheses.

This is strictly a **Fourier-side** conditional result. A faithful bridge
to the physical homogeneous Sobolev seminorm in the published result and
to the local strong solution class remains open. Neither an external theorem
nor an unconditional global-regularity assertion is introduced here.
