# Canonical source-peak sharp sixth-root H3 dissipation optimization

Base commit: `e1c57ded0fe03ab8437d42ef1c30cd007410f18f` (unbounded actual physical dissipation amplification).

The prior physical Fourier spectral decomposition and kinetic ceiling give the exact sufficient condition

    8 * rho^6 * E0(b) <= ‖U3(t)‖²,  rho >= 1
      ==> (rho²/2) * ‖U3(t)‖² <= D3(t).

Take E = E0(b) >= 0 and A = ‖U3(t)‖. Above the checkable amplitude threshold A² >= 8(E+1), set

    x = A² / (8(E+1)),  rho = x^(1/6).

Mathlib's `Real.rpow_inv_natCast_pow` supplies rho^6 = x; `Real.one_le_rpow` yields rho >= 1. Because E <= E+1,

    8*rho^6*E <= 8*rho^6*(E+1) = A².

The actual physical dissipation inequality yields rho²*A²/2 <= D. Cubing preserves the inequality by nonnegativity. Multiply by 64(E+1) and rewrite the exact sixth-root equation to obtain

    A^8 <= 64*(E+1)*D^3,
    A^8/(64*(E+1)) <= D^3.

This is an explicit 8/3-growth law for the physical H4-type dissipation as a function of the actual weighted H3 spectral SUP norm, up to a fixed earlier physical kinetic anchor. It does NOT assume or establish any terminal-uniform time modulus; the physical moment is fixed and the cutoff is selected only in Fourier space. It is stronger quantitatively than the earlier arbitrary-constant ratio divergence.

The source-maximizer application reuses the exact original `h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244` witness. In the same conditional critical noncompression/linear-rate/outer-cutoff regime its peak norms diverge; eventually the explicit amplitude threshold holds after b=(a+T)/2. The theorem then proves A_k^8 <= 64*(E0(b)+1)*D3(s_k)^3 at the original source-maximizing s_k. No further subsequence or physical time selection is introduced.

This is pointwise superquadratic coercivity and NOT a contradiction with finite time-integrated dissipation. Even a large cubic dissipation power at an isolated time can have an arbitrarily short persistence duration. A quantitative PDE temporal persistence estimate or another integrated inequality remains necessary for closure.

Validation: Python syntax, missing theorem/placeholder audits, archive integrity, and registration idempotency. Lean compilation requires the user's repo environment.
