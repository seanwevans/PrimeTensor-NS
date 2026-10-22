# Physical eighth-moment reduction from the six-factor velocity escape

Base checkpoint: `d2a8c188` — physical eighth-moment six-factor escape.

## The six actual velocity inputs

The quantitative Young upper bound for the order-four convolution is a
product of raw Fourier L² factors with a weighted sum of eighth radial
raw Fourier moments and raw Fourier L¹ masses:

    convolution_4(U_k, U_j)^2 <= L2(U_k)*L2(U_j)*C8*
      (M8(U_k)*L1(U_j) + L1(U_k)*M8(U_j)).

Previous work proves that hypothetical escape of the actual fourth-radial
physical dissipation makes one of six constituent factors arbitrarily large
on every terminal subtail, under strict-time eighth-moment integrability.

## The new conditional reduction

The new module identifies indices 2 and 5 of the original `Fin 6` primitive
factorization with the actual *raw Fourier eighth-order moments* of the first
and second input velocity component. It bounds the remaining indices 0,1,3,4
using the genuine Fourier L², conjugate L², and Fourier L¹ velocity masses.
If all those lower-order factors possess a common strict-time upper ceiling
`B`, choose the previous primitive escape threshold `max B K + 1`.
The selected factor cannot be a low one, since that would contradict the
ceiling; consequently it must be one of the two eighth-order factors.

This yields the exact conditional obstruction

    (top D3 unbounded, raw M8 integrable at strict times,
     uniform low Fourier L1/L2 ceiling)
     => (for every late subtail and K,
         some actual component velocity M8 exceeds K).

## Important limitations

Neither eighth-moment integrability nor the uniform low Fourier L¹ ceiling
is derived here from the physical Navier–Stokes PDE. Fourier L² kinetic
control alone does not imply uniform Fourier L¹ without further high-frequency
information. The index of the escaping velocity component may vary with the
subtail and threshold. No terminal-uniform high-moment bound or continuation
theorem follows from this reduction by itself.

## Next mathematical problem

Use the existing physical kinetic energy ceiling and Sobolev/weighted Fourier
inequalities to replace the explicit lower-factor premise by a proved
bound under the relevant endpoint regularity assumptions; separately
reconcile strict-time eighth-moment integrability with the actual H³
smooth-time path hypotheses. Avoid interpreting the conditional reduction as
an unconditional eighth-moment escape theorem.
