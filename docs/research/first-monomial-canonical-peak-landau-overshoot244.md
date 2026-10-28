# Canonical physical H³ transport spike: Landau ceiling and forced overshoot

Base: `d3bf94f5` (verified against GitHub). The committed transport-spike theorem forces a witness q in the genuine half-loss interval s≤q≤r with

    H A² < 8(B+1) Tr₃(q),
    A^8 = 16384 (E₀(b)+1) H³.

The pointwise physical transport estimate already in the repository is

    Tr₃(q) ≤ |Tr₃(q)| ≤ 4422 (1+C₁ sqrt(E₃(q))) E₃(q).

The spectral peak amplitude `A` is a three-component product SUP norm, not the square root of the full H³ energy. The exact identity `E₃(s)=1+Σⱼ‖Gⱼ(s)‖²` and existing sharp finite-component bound yield `E₃(s)≤1+3A²`. For `A≥2`, if the spike occurs without physical H³ energy overshooting its starting value, then

    E₃(q) ≤ E₃(s) ≤ 1+3A² ≤ 4A²,
    sqrt(E₃(q)) ≤ 2A.

Multiplication by the positive budget factor and cancellation of `A²>0` yield

    H < 32(B+1) 4422 (1+2C₁ A).

Hence **fast optimized clocks** exceeding this explicit threshold force actual H³ energy overshoot at the SAME point q:

    E₃(q)>E₃(s).

The four-theorem module proves an abstract scalar inequality, a bridge to actual signed physical H³ transport, a fast-clock specialization, and the original canonical optimized-peak terminal-compression/half-loss alternative with the overshoot-versus-slow-clock disjunction. No source peak is reselected, and the old exact fourteenth-power rate constraint is preserved.

This does not show that an overshoot is impossible. A subsequent step must compare the very short optimized window to the one-sided autonomous H³ growth estimate; one may obtain further restrictions without assuming a uniform terminal transport bound. No unconditional continuation theorem is asserted.

Validation: Python syntax and idempotence of registrar, ZIP integrity, source placeholders and theorem-name checks. The Lean toolchain is not accessible in this execution environment; run the provided `lake` build and full audit locally.
