# Canonical H³ peak half-loss forces a physical signed transport spike

Base commit `75c1a253`: automatically integrable full physical signed H³ transport at the **original** canonical source peaks.

Let `A = ‖h3AuditActualSpectralVelocityTotal hH3 s‖`, `E = velocityH3Energy0At u b`, and let `B = ∫_a^T velocityH3DissipationAt u t dt ≥ 0` be the total finite physical H³ dissipation budget. The optimized peak floor gives an actual `H > 0` satisfying

    A^8 = 16384*(E+1)*H^3.

The earlier theorem establishes the unchanged conditional canonical alternative:

- The remaining physical time is compressed: `T-s ≤ (B+1)/H`; or
- An actual half-loss observation `r` occurs with `s < r ≤ s+(B+1)/H < T`, and the **automatically integrable signed physical transport** obeys

      A²/8 < ∫_s^r Transport₃(t) dt.

The new generic interval lemma compares the signed transport with its constant-height rectangle. With no continuity of transport in time, it produces **an actual point `q ∈ [s,r]`** satisfying

    H*A² < 8*(B+1)*Transport₃(q).

The right-hand side is strictly positive, so the physical signed transport at this point is necessarily positive whenever `A > 0`. Cubing and substituting the exact optimized identity gives the root-free inequality

    A^14 < 8388608*(E+1)*(B+1)^3 * Transport₃(q)^3.

The cofinal theorem preserves the identical original source-maximizing times, annulus witnesses, summability, and conditional sixth/ninth-eighth critical-width regime. The new `q` is selected within the actual half-loss interval; it is not a substitute source maximizer.

This is a **necessary positive transport-rate lower bound** in the noncompressed branch. It is not a physical transport upper estimate, terminal contradiction, unconditional critical-width theorem, or Navier–Stokes regularity proof. The next analytic challenge is to control the positive signed full third-order transport independently of peak growth.

Validation: theorem source is free of `sorry`, `admit` and new axioms; package/registrar static checks and idempotence have been run. Actual Lean elaboration and build require the pinned project toolchain on the user's machine.
