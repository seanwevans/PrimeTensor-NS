# Canonical physical source peak: viscous or positive signed-transport drain

Base commit: `a24052bb` (actual signed physical H³ energy drain after the original source-peak half-loss alternative).

The previous exact energy balance and mean-value theorem, at the original canonical source peak `s` with amplitude `A = ‖U₃(s)‖`, produce `s < q < r` with

    A²/4 < (r-s) (2 D₃(q) + Transport₃(q)).

The budget clock, **not an arbitrary continuity interval**, is `L = (B+1)/H` with `B = ∫_a^T D₃(t) dt`, `r-s ≤ L`, `H > 0` and the exact optimized identity

    A⁸ = 16384 (E₀(b)+1) H³.

The signed drain rate must therefore obey

    H A² < 4 (B+1) (2 D₃(q) + Transport₃(q)),

hence the exact physical channel alternative

    H A² < 16 (B+1) D₃(q)

**or**

    H A² < 8 (B+1) Transport₃(q).

The second branch forces positive signed transport. Neither branch is excluded by the known physical H³ estimates. The normalized signed rate also satisfies the polynomial consequence

    A¹⁴ < 1048576 (E₀(b)+1) (B+1)³ (2 D₃(q) + Transport₃(q))³.

`h3Path_noL2Trace_canonicalWidth_sourcePeakSignedDrainSplit244` transports these conclusions to the **same** existing canonical source-maximizing times under the unchanged explicit conditional noncompression/sixth/ninth-eighth critical-width hypotheses; it does not reselect peak times, prove a uniform physical-time modulus, assume the sign of transport, or assert a Navier–Stokes regularity contradiction. The remaining hard frontier is an independent physical PDE bound on the **positive signed H³ transport** or the instantaneous viscous drain at the intermediate time.

Validation: static source checks and registrar-idempotence checks only; Lean compilation must be performed in the user's repository.
