# Signed sixth flux: cofinal original-gap physical dissipation compression

Baseline: `21a68a308e02edaa1820d42b8fc20434c4a6512a` — closed-gap signed flux alternatives with backward kinetic PDE charge.

## Mathematical advance

The prior proof ensures an adverse imaginary signed LowMax(R) sixth-flux difference on a strict physical kinetic gap `[x,y]` is paid by either an amplitude-weighted Schwartz recovery/source clock or a genuine positive-width annular viscous interval **inside that same gap**. The remaining obstacle is to quantify what happens along the original cofinal separated family with finite physical H3 dissipation.

First, for a nonnegative real density `D` integrable on `[a,T]`, any nested cofinal subintervals `[x_k,y_k] ⊂ [a,T]` with `x_k→T` satisfy `∫_[x_k,y_k] D → 0`. The proof uses the existing terminal integral/primitive theorem plus interval monotonicity, not a pointwise bound on `D`.

Second, apply that fact to the **original kinetic gaps**

`x_k = tau(v k) + delta(v k)`, `y_k = tau(v(k+1))`.

The original natural-annular witness ensures `delta(v k)>0`, `x_k<T` and `tau(v k)→T`. Thus `x_k→T`, and strict separation places `[x_k,y_k]` inside the original physical interval. Under the existing finite full H3 dissipation hypothesis,

`Dgap_k = ∫_[x_k,y_k] velocityH3DissipationAt(u,r) dr → 0`.

No new physical times or cutoffs are selected in proving this limit.

## Actual cofinal signed-flux gate

Assume a specific indexed family of two Schwartz recovery profiles `p_k,q_k`, their actual Fourier weighted-H3 states `V_k,W_k`, and two selected strict gap times `s_k,t_k`. Require exact a.e. Fourier realization, closed-gap membership and an adverse signed imaginary increment at the *moving* LowMax cutoff `R_k`:

`eta ≤ |Im Phi_(R_k)(p_k) - Im Phi_(R_k)(q_k)|`, for `eta>0`.

Define the exact amplitude coefficient and viscous height

`A_k = 243 [2(R_k+1)]^7 C0 (1+||V_k||+||W_k||)^3`;

`H_k = (R_k+1)^2 (eta/4)^2 / [2(A_k^2+1)] > 0`.

The new cofinal theorem proves for every `epsilon>0` and every sufficiently late **original** kinetic gap:

1. `eta/2 < A_k*(||V_k-U(t_k)|| + C_(R_k)*SourceL1Gap_k + ||U(s_k)-W_k||)`; or
2. there is an actual signed observation time `z=s_k` or `z=t_k` and a strictly positive physical annular persistence width `w_k` in the *same* gap such that `w_k * H_k/4 < epsilon`.

The selected window remains either forward-inside or backward-inside the very same gap, respecting the right-endpoint case. The conclusion is quantitative for arbitrary moving radii and varying Schwartz amplitudes. It **does not** infer `w_k→0` because `H_k` can vanish, or a contradiction with finite dissipation.

## Missing input and logical scope

The project's existing `ThirdFullKineticGapArbitraryRadialTradeoff244` supplies, for one adverse physical time, a real-solenoidal Schwartz recovery sequence with a signed one-snapshot alternative. It does NOT by itself produce a persistent **difference** of two signed LowMax recoveries at times `s_k,t_k` or a uniform positive `eta`. Accordingly `ThirdFullKineticSignedLowMaxCofinalGapSamples244` is an explicit additional predicate, not claimed automatic from no-H3-trace.

The next hard mathematical task is to manufacture and synchronize those two-snapshot adverse samples from the original signed replenishment mechanism, with weighted recovery errors controlled relative to `eta` and the cubic amplitude/radius, and to rule out width-height collapse rather than merely assert smallness of the gap integral.

## Verification

Registrar checks one predicate and three theorems, and adds the exact source import plus audit declarations. Regenerate `proof/generate_index.py` before compiling with the pinned Lean/mathlib toolchain. Static ZIP and registrar tests are not Lean kernel verification.
