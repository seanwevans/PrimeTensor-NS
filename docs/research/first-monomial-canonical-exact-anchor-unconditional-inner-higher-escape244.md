# Canonical exact-anchor unconditional inner radial moment escape

Base `f44380de`: derive universal top higher radial escape from persistent canonical H3 charge.

## New mathematical bridge

The original cubic annulus at anchor `t_k=τ(v k)` is between **inner** radial frequency `R_k=v(k)+1` and **outer** `Q_k=N(v k)+1`. Its actual surplus satisfies

`(L_{Q_k}-L_{R_k})(t_k) - R_k^3/2 > R_k^3/4`.

By the two exact physical low/high Fourier partitions and `H_{Q_k}(t_k)≥0`, the inner physical high tail dominates the annular mass:

`H_{R_k}(t_k) ≥ L_{Q_k}(t_k)-L_{R_k}(t_k) > 3 R_k^3/4`.

The previously verified full-to-top-order physical bridge at radius `R_k≥1` gives, for every natural `m`, the actual **existing** extended moment

`ofReal(((R_k²)^m) * (3 R_k³/16)) ≤ M⁺_{4+m}(t_k)`.

Strict monotonicity of the original canonical extraction gives `R_k³→+∞`, hence the extended moments `M⁺_{4+m}(t_k)→+∞` for *each fixed m* on **one original canonical sequence**, with no additional persistent height-width charge hypothesis. This is a stronger conclusion than the previous conditional universal-moment theorem. It is compatible with finite integrated H³ dissipation because the original canonical windows shrink, and it does not prove or refute singularity.

Crucially, this theorem refers to **inner cutoff** `R_k`, not to outer cutoff `Q_k`; it does not unconditionally conclude the near-total outer-tail fraction. The hypotheses remain logged preterminal H³ admissibility, physical H³ energy class, positive terminal kinetic mass, no terminal physical L² trace, and finite full H³ time-integral.

Declarations:
- `h3Path_scalar_annulus_le_innerHighTail244`
- `h3Path_exactAnchor_innerHighTail_cubicFloor244`
- `h3Path_exactAnchor_innerCubic_forces_topHigherMoment244`
- `h3Path_scalar_cubicLower_forces_allTopMomentEscape244`
- `h3Path_noL2Trace_exactAnchor_unconditionalInnerHigherEscape244`

No `sorry`, `admit`, or new `axiom` intended. Pinned Lake/Lean compilation unavailable here; must be checked in the user's repository.
