# Quarter triad: exact scalar-window transfer

**Checkpoint:** `30123f81`, *identify coherent triad orbit and localize narrow Schwartz support*.

Define the original fixed-width real-compatible solenoidal Schwartz Fourier field `U`, and for an arbitrary real scalar frequency function `w`, let

`V_w(ξ) = w(ξ) U(ξ)`.

The six-order trilinear symbol is exactly cubic in its amplitude slots. Thus, on the momentum plane `q = -p-r`, with `F_U = Re(i C_6(U(p),U(q),U(r)))`,

`F_{V_w}(p,r) = w(p) w(q) w(r) F_U(p,r)`.

This equation applies to **every one of the six ordered contributions** and makes no assumption that replacing the original bump profile leaves `F_U` unchanged. If `w` is nonnegative and its three factors are nonzero, positivity of the reference kernel transfers without cancellation.

This patch proves the scaling law, nonnegative / strictly positive transfer, zero-on-vanishing-factor, and sign transfer on a coherent positive tube. It **does not** yet construct the final even, smooth, compactly supported window, or prove the unlocalized integral nonzero. These remain explicit, rather than hidden hypotheses. An even window is needed to retain real-valued physical data, and a compact smooth window gives a Schwartz multiplier.

**Next step:** construct the even nonnegative window from narrow bumps at the six centers; show its momentum support lies in the coherent tube while it is positive at one resonant center; then integrate using the kernel's compact support and continuity.
