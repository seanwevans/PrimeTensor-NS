#!/usr/bin/env python3
"""Static audit of fixed-cube, two-cutoff Wiener compactness reduction."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE_PATH = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
                    'FullThirdSolenoidalKineticThreeBandZ3GalerkinFixedCoreCompactness.lean')
DOC = ROOT / 'docs/research/z3-galerkin-fixed-core-compactness-2026-11-17.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_fixed_core_compactness.py'
code = CODE_PATH.read_text(encoding='utf-8')
assert DOC.is_file() and REG.is_file()
for name in (
    'thirdFullThreeBand_z3WienerTail_twoRadius244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3GalerkinFiniteExtend_off244',
    'Finset.sum_filter_add_sum_filter_not',
    'Finset.sum_le_sum_of_subset_of_nonneg',
    'Fintype.piFinset',
    'thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244',
    'thirdFullThreeBand_z3Galerkin_exists_twoCutoff_fixedCore244',
):
    assert name in code, name
scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert 'Real.exp (-(Real.log (9 / 5' in code
assert 'thirdFullThreeBandZ3GalerkinFixedCoreCube244 N' in code
assert len(re.findall(r'(?m)^theorem\s+thirdFullThreeBand_', code)) == 8
print('PASS: actual finite fields; common Fourier cube; 200 exponential tail; no assumed limit')
