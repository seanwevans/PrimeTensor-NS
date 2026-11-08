# Signed low-maximum sixth flux: physical source clock and unavoidable high tails

Base: `b1f9873482bce93acbacda9038cf66eb535087bd` — finite-radius weighted-H³ Lipschitz continuity for the actual complex signed sixth-flux integral.

## Exact mismatch resolved

The established complex flux estimate uses the *full* difference of two weighted-H³ spectral representatives. The existing physical momentum FTC instead gives only the sharp low-band difference. Treating these as equal would silently assume terminal tightness of the H³ high tails.

Write `U_t = h3AuditActualSpectralVelocityTotal hH3 t`, `U_s = h3AuditActualSpectralVelocityTotal hH3 s`, and `V,W` for two independently chosen Schwartz weighted representatives. For the **actual** sharp projector `Q_R` and its complementary highpass `P_R`, the triangle inequality and exact low/high decomposition give

`‖V−W‖ ≤ ‖V−U_t‖ + ‖Q_R U_t−Q_R U_s‖ + ‖P_R U_t‖ + ‖P_R U_s‖ + ‖U_s−W‖`.

The physical Navier–Stokes Hilbert momentum FTC proves at any strict ordered physical times `s ≤ t` that

`‖Q_R U_t−Q_R U_s‖ ≤ C_R ∫_[s,t] ‖physical projected source(r)‖ dr`,

with `C_R = thirdFullFiniteBandH3WeightCeiling244 R`, the previously formalized exact finite-band W₃ coefficient.

Combining this with the previous genuine complex signed Lipschitz theorem yields

`‖Φ_R(v)−Φ_R(w)‖ ≤ 243 [2(R+1)]⁷ C₀ (1+‖V‖+‖W‖)³ × [‖V−U_t‖ + C_R∫_[s,t]‖source‖ + ‖P_R U_t‖ + ‖P_R U_s‖ + ‖U_s−W‖]`.

This is an actual two-time physical PDE **source/tail** estimate of the signed complex Fourier flux of the two Schwartz recovery profiles, with no assumed full-H³ time derivative or Schwartz selection in time. A separate theorem bounds the signed imaginary parts, retaining the physical phase convention.

## Same bound across whole strict kinetic gaps

The project's existing `thirdFullPhysical_strictGap_uniformLowBandPDEModulus244` bounds the low-band distance for *any* two samples in one strict physical gap by its complete projected-source L¹ action on the gap. This patch composes that precise theorem with the same high tails and recovery errors. Time order within the gap is irrelevant.

## What this does **not** prove

The signed LowMax(R) region has frequency-gradient threshold `2(R+1)` whereas the `Q_R` projector has threshold `R+1`. The high-tail correction here is therefore mathematically necessary, not an artifact of a notation change. Neither the source action becoming small nor fixed-band freezing alone proves the full signed flux freezes. A positive flux excursion must be paid by one of: physical source action, actual H³ high tails, or approximation error. Proving an effective tail alternative along the original kinetic gaps, and then relating it to the existing dissipation charges, is the next hard-math task.

No claim is made about terminal-uniform H³ bounds, radius-independent estimates, or Navier–Stokes continuation.

## Verification

The registrar registers four public theorems with `#check` and `#print axioms`. Regenerate `proof/generate_index.py`, compile the new Lean module, build the project, and check proof fragments before committing. These are local obligations; static archive verification is not kernel verification.
