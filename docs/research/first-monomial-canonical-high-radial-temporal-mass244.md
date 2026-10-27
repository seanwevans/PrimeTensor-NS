# Canonical source maxima: high-radial Fourier spatial concentration and temporal concentration

**Base:** `30431ec5` — quantify canonical projected source exposure in finite radial spectral clocks.

**New:** `FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialTemporalMass244.lean`.

## 1. Exact weighted state-energy distinction

The repository's `H3SpectralVelocityState` is `Fin 3 → H3SpectralScalarState`, with the **sup** norm, while the Plancherel square energy is the **sum** of three coordinate norm squares. Thus, not equality but

    ‖G‖² ≤ h3SpectralVelocitySquareEnergy G = Σ_j ‖G j‖².

The proof uses `pi_norm_le_iff_of_nonneg` and the existing finite-coordinate energy bounds.

## 2. Exact genuine Fourier integral splitting

For two spectral snapshots G,H, define

    HighTemporal_ρ(G,H) = ∫_{|Dξ|≥ρ} Σ_j |G_j(ξ)−H_j(ξ)|² dξ.

The preexisting radial defect is the integral over |Dξ|<ρ, and the new theorem proves

    LowDefect_ρ(G,H) + HighTemporal_ρ(G,H)
      = h3SpectralVelocitySquareEnergy(G−H).

This follows from `Lp.coeFn_sub`, the already proven exact total spectral Fourier-energy identity, and `setIntegral_compl` for the measurable radial-frequency ball. No pointwise representative identification is used at a single fixed frequency.

## 3. Full norm escape and bounded low mass imply high-integral escape

A generic theorem proves that when ‖G_k−H_k‖→∞ and the low-radial squared defect stays bounded, the **actual complementary squared difference integral** tends to infinity. Another theorem replaces bounded low defect with vanishing low defect. A separate theorem handles one-state high-radial mass when only ‖G_k‖ diverges and low-radial state mass is bounded.

## 4. Same canonical PDE witnesses

From the previously committed fixed source-maximizing time sequence s_k and window anchors t_k=τ(v_k), retain the disjoint summability and the conditional noncompression/linear-rate/critical-width regime. Within that regime, the already-proven spectral state peak escape ‖U₃(s_k)‖→∞ and kinetic monotonicity imply, for **each fixed radial cutoff** ρ,

    ∫_{|Dξ|≥ρ} Σ_j |U₃(s_k)_j(ξ)|² dξ →∞.

This part **does not assume** vanishing source exposure.

If in addition the exposure `C(v_k)·(T−t_k)/2→0` and the anchor spectral norms are eventually bounded, then the radial temporal modulus gives low-radial square-defect convergence to zero, while the already-proven spectral peak/anchor increment lemma gives full spectral displacement divergence. The exact splitting implies

    ∫_{|Dξ|≥ρ} Σ_j |U₃(s_k)_j(ξ)−U₃(t_k)_j(ξ)|² dξ →∞.

Both statements hold on the **same chosen times** and keep all additional branch hypotheses explicit.

## 5. Limits

Neither spatial high-frequency escape nor high-frequency temporal displacement divergence is by itself a contradiction to finite time-integrated H³ dissipation. A time-persistence / absolute-continuity cost estimate on *disjoint* windows remains necessary. The canonical source-maximizing half-terminal windows may overlap. No Navier–Stokes regularity or continuation is claimed.
