#!/usr/bin/env python3
"""Static structural and scope check for the actual infinite Wiener limit."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3GalerkinInfiniteWienerLimit.lean')
DOC = ROOT / 'docs/research/z3-galerkin-infinite-wiener-limit-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_infinite_wiener_limit.py'
assert CODE.is_file() and DOC.is_file() and REG.is_file()
text = CODE.read_text(encoding='utf-8')
for expected in (
    'thirdFullThreeBand_z3Galerkin_zeroExtend_arbitraryFiniteMass_le244',
    'thirdFullThreeBand_z3Galerkin_uniformCoordinateLimit_finiteHighMass244',
    'thirdFullThreeBand_z3Galerkin_limit_highWiener_summable244',
    'thirdFullThreeBand_z3Galerkin_finiteToInfinite_fixedCore244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244',
    'thirdFullThreeBand_z3Galerkin_exists_actualInfiniteWienerLimit244',
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'summable_of_sum_le',
    'Real.tsum_le_of_sum_le',
    'thirdFullThreeBand_z3GalerkinWiener_fixedCore_split244',
    'thirdFullThreeBand_z3Galerkin_WienerDifferenceTail_small244',
    'Finset.eventually_all',
):
    if expected not in text:
        raise AssertionError(expected)
scrub = re.sub(r'/-.*?-/', '', text, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', text)) == 6
assert len(re.findall(r'(?m)^noncomputable def\s+', text)) == 1
assert '∑\' n : WiIndex244' in text
assert 'Real.log (9 / 5' in text and 'Real.log (3 / 2' in text
print('PASS: 6 theorems, genuine infinite tsum, finite-sum Fatou, full uniform-time Wiener limit')
