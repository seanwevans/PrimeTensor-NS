# Real physical Schwartz approximation from weighted H³ spectral state

Baseline commit: `78edea25` (October 17, 2026).

## Unconditional analytical bridge

The existing weighted spectral raw-Fourier approximation constructs a complex
Schwartz frequency function `S` approximating `rawFourierL2(G)` in `L²`.
Mathlib's Schwartz inverse-Fourier identity and the continuous real-part
projection produce a **real Schwartz physical function**
`h3RawSchwartzPhysicalRealInverse244 S`. The new comparison proves

  ‖decodeReal(G) - physicalRealSchwartz(S).toLp‖
      ≤ ‖rawFourierL2(G) - S.toLp‖.

The new density and diagonal selection theorems construct a simultaneous
three-component REAL Schwartz sequence converging to the full real physical
L² decoder of any spectral H³ velocity state. For compatible actual physical
velocity snapshots, the target is identified with actual `h3JetSlot0` data.

## Remaining hard-math obligations

The constructed real Schwartz sequence is only asserted to converge in
physical **L²**. It is **not yet** proved to be Cauchy in the complete E₂/E₃
physical derivative graph. For that, use smooth compact *weighted* spectral
approximants, deweight, enforce Fourier reality, and prove equality/continuity
of all the ordered spatial derivative L² representatives. The solenoidal
constraint and identification of the completed 243-slot transport observable
with actual physical trilinear transport are also still unproved by this patch.
