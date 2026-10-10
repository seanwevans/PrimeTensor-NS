import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightOneSidedEnergyPairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Weak.Compact.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Initial weak H³ correlations from genuine raw Fourier L² convergence

At a strict time the actual H³ velocity encoder stores W₃ times the Fourier
transform of the genuine zeroth-order physical velocity. Its deweighted L²
state is exactly that physical Fourier transform, with no proxy variables.

For every smooth compact *weighted* H³ spectral test G, the pairing with a
weighted state F equals the unweighted L² pairing of its raw Fourier state
with the reweighted smooth compact test W₃G. Consequently, strong convergence
of the raw Fourier L² state gives convergence of every compact H³ pairing.

A uniform H³ bound on an initial right subfilter permits extension to an
arbitrary H³ test by smooth compact density and Cauchy--Schwarz. In particular,
only the three correlations against the initial H³ spectral components are
needed. Their sum supplies the lower-correlation half of the preceding
one-sided polarization criterion.

The physical upper-energy inequality automatically supplies the uniform bound.
Raw physical L² right convergence and the upper H³ energy inequality remain
explicit initial-value hypotheses; the open-time PDE class does not imply them.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace
  ComplexConjugate ContDiff SchwartzMap

noncomputable section

-- The Fourier carrier is a finite PiLp product. Local Fintype evidence must
-- be reinstated in each module; instances from imported files are local.
noncomputable local instance axisFintypeH3AuditInitialRawL2WeakH3Trace
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Moving the real H³ weight across a complex Fourier L² pairing, for an
arbitrary spectral state and a smooth compact weighted test. -/
theorem h3Audit_inner_spectral_smoothCompact_eq_rawFourier_reweighted
    (F G : H3SpectralScalarState)
    (g : H3FourierPoint3 → ℂ)
    (hG : (G : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    inner ℂ F G =
      inner ℂ (h3SpectralScalarRawFourierL2 F)
        ((h3SmoothCompactReweightedSchwartz g hcompact hsmooth).toLp
          2 (volume : Measure H3FourierPoint3)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    h3SpectralScalarRawFourier_reweight_ae F,
    h3SpectralScalarRawFourierL2_ae F,
    hG,
    SchwartzMap.coeFn_toLp
      (h3SmoothCompactReweightedSchwartz g hcompact hsmooth)
      2 (volume : Measure H3FourierPoint3)
  ] with ξ hReweight hRaw hTest hWeighted
  rw [← hReweight, hTest, hWeighted,
    h3SmoothCompactReweightedSchwartz_apply, hRaw]
  change
    inner ℂ
      ((h3SobolevFrequencyWeight ξ : ℂ) •
        h3SpectralScalarRawFourier F ξ)
      (g ξ) =
    inner ℂ (h3SpectralScalarRawFourier F ξ)
      ((h3SobolevFrequencyWeight ξ : ℂ) • g ξ)
  rw [inner_smul_left, inner_smul_right]
  simp

/-- Raw Fourier L² convergence forces the weak H³ pairing limit against
any smooth compact H³ test, with no H³ boundedness assumption. -/
theorem h3Audit_tendsto_initialCompactPairing_of_rawL2
    (F : ℝ → H3SpectralScalarState)
    (G₀ G : H3SpectralScalarState)
    (hRaw : Tendsto (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralScalarRawFourierL2 G₀)))
    (hCompact : H3SpectralScalarHasSmoothCompactRepresentative G) :
    Tendsto (fun t : ℝ => (inner ℂ (F t) G).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ G₀ G).re) := by
  obtain ⟨g, hG, hSupport, hSmooth⟩ := hCompact
  let Ψ : H3FourierComplexL2 :=
    (h3SmoothCompactReweightedSchwartz g hSupport hSmooth).toLp
      2 (volume : Measure H3FourierPoint3)
  have hMap : Continuous (fun W : H3FourierComplexL2 =>
      (inner ℂ W Ψ).re) :=
    Complex.continuous_re.comp (continuous_id.inner continuous_const)
  have hRawPair :
      Tendsto (fun t : ℝ =>
        (inner ℂ (h3SpectralScalarRawFourierL2 (F t)) Ψ).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℂ (h3SpectralScalarRawFourierL2 G₀) Ψ).re) :=
    hMap.continuousAt.tendsto.comp hRaw
  have hFunctions :
      (fun t : ℝ => (inner ℂ (F t) G).re) =
      (fun t : ℝ =>
        (inner ℂ (h3SpectralScalarRawFourierL2 (F t)) Ψ).re) := by
    funext t
    exact congrArg Complex.re
      (h3Audit_inner_spectral_smoothCompact_eq_rawFourier_reweighted
        (F t) G g hG hSupport hSmooth)
  have hTarget :
      (inner ℂ G₀ G).re =
        (inner ℂ (h3SpectralScalarRawFourierL2 G₀) Ψ).re :=
    congrArg Complex.re
      (h3Audit_inner_spectral_smoothCompact_eq_rawFourier_reweighted
        G₀ G g hG hSupport hSmooth)
  rw [hFunctions, hTarget]
  exact hRawPair

/-- Extend the raw L² weak-pairing limit from compact H³ tests to the
initial H³ state itself, using an EVENTUAL H³ norm bound. -/
theorem h3Audit_tendsto_initialCorrelation_of_rawL2_and_eventualH3Bound
    (F : ℝ → H3SpectralScalarState)
    (G₀ : H3SpectralScalarState)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hBound : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), ‖F t‖ ≤ B)
    (hRaw : Tendsto (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralScalarRawFourierL2 G₀))) :
    Tendsto (fun t : ℝ => (inner ℂ (F t) G₀).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ G₀ G₀).re) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let D : ℝ := B + ‖G₀‖ + 1
  have hD : 0 < D := by
    dsimp only [D]
    have hn := norm_nonneg G₀
    linarith
  let η : ℝ := ε / (4 * D)
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨G, hCompact, hApprox⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G₀ hη
  have hCompactLimit :
      Tendsto (fun t : ℝ => (inner ℂ (F t) G).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ G₀ G).re) :=
    h3Audit_tendsto_initialCompactPairing_of_rawL2 F G₀ G hRaw hCompact
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      dist (inner ℂ (F t) G).re (inner ℂ G₀ G).re < ε / 2 :=
    (Metric.tendsto_nhds.mp hCompactLimit) (ε / 2) (by positivity)
  have hEtaEq : D * η = ε / 4 := by
    dsimp only [η]
    field_simp [ne_of_gt hD]
  have hBoundPair : B * ‖G₀ - G‖ < ε / 4 := by
    calc
      B * ‖G₀ - G‖ ≤ D * ‖G₀ - G‖ :=
        mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith [norm_nonneg G₀])
          (norm_nonneg _)
      _ < D * η := mul_lt_mul_of_pos_left hApprox hD
      _ = ε / 4 := hEtaEq
  have hTargetPair : ‖G₀‖ * ‖G₀ - G‖ < ε / 4 := by
    calc
      ‖G₀‖ * ‖G₀ - G‖ ≤ D * ‖G₀ - G‖ :=
        mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) (norm_nonneg _)
      _ < D * η := mul_lt_mul_of_pos_left hApprox hD
      _ = ε / 4 := hEtaEq
  filter_upwards [hBound, hNear] with t ht hClose
  have hFirst :
      dist (inner ℂ (F t) G₀).re (inner ℂ (F t) G).re < ε / 4 := by
    calc
      _ ≤ ‖F t‖ * ‖G₀ - G‖ :=
        dist_re_inner_right_le_norm_mul_norm_sub (F t) G₀ G
      _ ≤ B * ‖G₀ - G‖ :=
        mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ < ε / 4 := hBoundPair
  have hLast :
      dist (inner ℂ G₀ G).re (inner ℂ G₀ G₀).re < ε / 4 := by
    rw [dist_comm]
    exact (dist_re_inner_right_le_norm_mul_norm_sub G₀ G₀ G).trans_lt
      hTargetPair
  calc
    dist (inner ℂ (F t) G₀).re (inner ℂ G₀ G₀).re ≤
        dist (inner ℂ (F t) G₀).re (inner ℂ (F t) G).re +
        dist (inner ℂ (F t) G).re (inner ℂ G₀ G₀).re :=
      dist_triangle _ _ _
    _ ≤ dist (inner ℂ (F t) G₀).re (inner ℂ (F t) G).re +
        (dist (inner ℂ (F t) G).re (inner ℂ G₀ G).re +
         dist (inner ℂ G₀ G).re (inner ℂ G₀ G₀).re) := by
      have hTri :
          dist (inner ℂ (F t) G).re (inner ℂ G₀ G₀).re ≤
            dist (inner ℂ (F t) G).re (inner ℂ G₀ G).re +
            dist (inner ℂ G₀ G).re (inner ℂ G₀ G₀).re :=
        dist_triangle _ _ _
      exact add_le_add (le_refl _) hTri
    _ < ε := by linarith

/-- At a strict time, raw Fourier deweighting of the whole actual spectral
velocity gives the zeroth-order Fourier transform of the genuine velocity. -/
theorem h3Audit_actualFullRawFourier_eq_physicalZeroJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (j : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) =
    h3ScalarFourierL2
      (velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0 j)) := by
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  change h3SpectralScalarRawFourierL2
    (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
      velocityH3BaseFourierAt u t hInt hMeas j
  exact h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    hFourier j

/-- A single physical H³ upper-energy inequality and a right raw-Fourier-L²
trace to a proposed H³ initial datum. By the preceding theorem, the raw
Fourier variables are exactly those of the actual old physical velocity. -/
def H3AuditInitialRightPhysicalRawL2AndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ U₀ : H3SpectralVelocityState,
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t <
          1 + h3SpectralVelocitySquareEnergy U₀ + ε) ∧
    (∀ j : Fin 3,
      Tendsto (fun t : ℝ => h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 t j))
        (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralScalarRawFourierL2 (U₀ j))))

/-- Near zero, the physical energy inequality gives a uniform bound on
all three actual weighted Fourier coordinates. -/
theorem h3Audit_initialEnergyUpper_eventually_spectralCoordinateBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hEnergyUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t <
          1 + h3SpectralVelocitySquareEnergy U₀ + ε) :
    ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      ∀ j : Fin 3,
        ‖h3AuditActualSpectralVelocityTotal hH3 t j‖ ≤
          Real.sqrt (2 + h3SpectralVelocitySquareEnergy U₀) := by
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hUpper := hEnergyUpper 1 (by norm_num)
  filter_upwards [hPositive, hBeforeT, hUpper] with t ht0 htT hBound
  intro j
  let ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  have hCoord := h3SpectralFinVector_coordinate_norm_le
    (h3AuditActualSpectralVelocityAt hH3 t ht) j
  have hState := h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy
    hH3 t ht
  have hE : velocityH3EnergyAt u t ≤
      2 + h3SpectralVelocitySquareEnergy U₀ := by
    linarith
  exact (hCoord.trans hState).trans (Real.sqrt_le_sqrt hE)

/-- Raw L² initial velocity convergence, together with the physical energy
upper inequality, discharges the former aggregate H³ correlation assumption. -/
theorem h3Audit_initialPhysicalRawL2AndEnergyUpper_implies_lowerCorrelation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hEnergyUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t <
          1 + h3SpectralVelocitySquareEnergy U₀ + ε)
    (hRaw : ∀ j : Fin 3,
      Tendsto (fun t : ℝ => h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 t j))
        (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralScalarRawFourierL2 (U₀ j)))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        h3SpectralVelocitySquareEnergy U₀ <
          h3AuditSpectralVelocityAggregateCorrelation
            (h3AuditActualSpectralVelocityTotal hH3 t) U₀ + ε := by
  let B : ℝ := Real.sqrt (2 + h3SpectralVelocitySquareEnergy U₀)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBound :=
    h3Audit_initialEnergyUpper_eventually_spectralCoordinateBound
      hH3 hT U₀ hEnergyUpper
  have hPair : ∀ j : Fin 3,
      Tendsto (fun t : ℝ =>
        (inner ℂ (h3AuditActualSpectralVelocityTotal hH3 t j) (U₀ j)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ (U₀ j) (U₀ j)).re) := by
    intro j
    exact h3Audit_tendsto_initialCorrelation_of_rawL2_and_eventualH3Bound
      (fun t => h3AuditActualSpectralVelocityTotal hH3 t j)
      (U₀ j) B hB (hBound.mono (fun t ht => ht j)) (hRaw j)
  have hPairSum :
      Tendsto
        (fun t : ℝ => h3AuditSpectralVelocityAggregateCorrelation
          (h3AuditActualSpectralVelocityTotal hH3 t) U₀)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3AuditSpectralVelocityAggregateCorrelation U₀ U₀)) := by
    change Tendsto
      (fun t : ℝ => ∑ j : Fin 3,
        (inner ℂ (h3AuditActualSpectralVelocityTotal hH3 t j) (U₀ j)).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ j : Fin 3, (inner ℂ (U₀ j) (U₀ j)).re))
    apply tendsto_finsetSum
    intro j _
    exact hPair j
  have hPairEnergy :
      Tendsto
        (fun t : ℝ => h3AuditSpectralVelocityAggregateCorrelation
          (h3AuditActualSpectralVelocityTotal hH3 t) U₀)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3SpectralVelocitySquareEnergy U₀)) := by
    simpa only [h3AuditSpectralVelocityAggregateCorrelation_self] using hPairSum
  intro ε hε
  have hNear := hPairEnergy.eventually
    (Ioi_mem_nhds
      (show h3SpectralVelocitySquareEnergy U₀ - ε <
        h3SpectralVelocitySquareEnergy U₀ by linarith))
  filter_upwards [hNear] with t ht
  linarith

/-- Initial raw physical L² velocity trace plus one-sided physical H³ energy
control implies the actual strong initial H³ Fourier trace. -/
theorem h3Audit_initialPhysicalRawL2AndEnergyUpper_implies_strongVelocityTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightPhysicalRawL2AndEnergyUpper hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨U₀, hUpper, hRaw⟩ := hData
  apply h3Audit_initialRightEnergyUpperCorrelationLower_implies_strongVelocityTrace
    hH3 hT
  exact ⟨U₀, hUpper,
    h3Audit_initialPhysicalRawL2AndEnergyUpper_implies_lowerCorrelation
      hH3 hT U₀ hUpper hRaw⟩

/-- Both transverse actual velocity components satisfy the full-time
intrinsic Sobolev estimate, conditional on the physical terminal endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalRawL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialRightPhysicalRawL2AndEnergyUpper hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T := lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  obtain ⟨U₀, hUpper, hRaw⟩ := hData
  have hLower :=
    h3Audit_initialPhysicalRawL2AndEnergyUpper_implies_lowerCorrelation
      hH3 hT U₀ hUpper hRaw
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOneSidedEnergyPairing
    hH3 hClass i hPhysical ⟨U₀, hUpper, hLower⟩

end
end Euclidean
end Bridge
end PrimeTensor
