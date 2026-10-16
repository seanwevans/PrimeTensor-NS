# Actual 27 second jets: quantitative homogeneous Sobolev

**Base:** `692913b6` — homogeneous whole-space Sobolev from cutoff limit.

The proven theorem `wholeSpaceC1FDerivL2ToL6_homogeneous_quantitative` is on `Point3`, whereas the 27 second derivative jets of the physical first monomial are Schwartz functions on the Euclidean `H3FourierPoint3` carrier. These are **not** definitionally the same normed space.

This increment explicitly pulls each jet back via the continuous linear equivalence `PiLp.continuousLinearEquiv`. The pulled-back function is a genuine `SchwartzMap Point3 ℝ`, so both `MemLp` inputs are discharged by `SchwartzMap.memLp` and `SchwartzMap.fderivCLM`. The physical `L⁶` norm is identified with the Euclidean `L⁶` norm using `PiLp.volume_preserving_toLp`. For every ordered component/axis triple `j,i,k`, the exact same universal Sobolev constant bounds the Euclidean L6 norm by the Point3 Frechet derivative L2 norm.

The remaining analytic step compares that physical Frechet derivative norm with the full 81-slot third-order energy, taking account of the distinct product-sup and Euclidean operator norms. This is deliberately **not** asserted here. No PDE hypothesis, axiom, or `sorry` is introduced.
