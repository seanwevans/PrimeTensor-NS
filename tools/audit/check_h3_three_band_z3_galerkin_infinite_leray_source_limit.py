#!/usr/bin/env python3
"""Static verification of source completion and exact finite Galerkin provenance."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
LEA = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
              'FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteLeraySourceLimit.lean')
DOC = ROOT / 'docs/research/z3-galerkin-infinite-leray-source-limit-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_infinite_leray_source_limit.py'
assert DOC.is_file() and REG.is_file()
code = LEA.read_text(encoding='utf-8')
for expected in (
    'thirdFullThreeBand_z3GalerkinAllOutputWienerBound244',
    'thirdFullThreeBand_z3TwoRadiusDerivativeEnvelope244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'Metric.cauchySeq_iff.mpr',
    'cauchySeq_tendsto_of_complete',
    'Real.tsum_le_of_sum_le',
    'summable_of_sum_le',
    'thirdFullThreeBand_z3Galerkin_exists_constructedInfiniteSourceLimit244',
    '(Real.log (5 / 4 : ℝ))',
    '50000',
):
    assert expected in code, expected
scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', code)) == 5
assert '∀ q : Finset IsIndex244' in code
assert '∀ᶠ k in atTop, ∀ t' in code
print('PASS: source completion / 50000 all-output mass / infinite weighted convergence')
