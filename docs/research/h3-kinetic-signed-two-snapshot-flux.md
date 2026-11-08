# Native signed sixth-flux: scaled two-snapshot weighted-H3 difference

Base commit: `58942f9bd73e3fa738034d6f1d70c7575a0ecc47`.

## Core mathematics

For two arbitrary complex three-component Schwartz fields `v,w`, write `D = v-w`. Their exact Fourier polarizations satisfy `P_D = P_v - P_w` by linearity of the Schwartz Fourier continuous linear map; a nonexistent `FourierTransform.fourier_sub` name is not used. If `V,W` are their actual weighted-H3 L2 spectral representatives, then `V-W` represents the weighted Fourier transform of `D` *a.e.*

The signed low-maximum sixth flux has an exact three-term complex polarization telescope:

`F(P_v,P_v,P_v)-F(P_w,P_w,P_w) = F(P_D,P_v,P_v)+F(P_w,P_D,P_v)+F(P_w,P_w,P_D)`.

By the previous commit, every mixed term is automatically integrable. The existing mixed Fourier Young/H3 theorem bounds its integral by

`M_R(s;a,b,c) = 9*[2(R+1)]^7 * ((3*s^2*a^2 + 3*s^(-2)*c^2)/2) * 3*C0*b`,

where `(a,b,c)` are the weighted H3 norms of first/middle/last inputs. Hence the exact signed integral difference is bounded by

`M_R(s1; δ,‖V‖,‖V‖) + M_R(s2; ‖W‖,δ,‖V‖) + M_R(s3; ‖W‖,‖W‖,δ)`,

with `δ=‖V-W‖` and *independent positive* scales. This retains the actual complex phases and the correct cutoff factor 2 in `2(R+1)`.

The scalings permit a linear modulus in δ for fixed V,W after balancing outer terms. The Lean theorem itself retains all scale choices and does not yet assert the optimized Lipschitz corollary, a physical PDE time estimate, a uniform-in-R estimate or Navier–Stokes continuation.

## Local verification

Run the guarded script against precisely the pinned base. The registrar adds the import and Lean `#check`/`#print axioms`, then `proof/generate_index.py` regenerates the source index before targeted build. The ZIP was assembled and Python-validated outside the user's pinned Lean environment; Lean elaboration remains to be confirmed by running the script.
