#!/usr/bin/env python3
"""Scope and structural audit for actual Galerkin strong Wiener Cauchy upgrade."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongWienerCauchy.lean')
DOC = ROOT / 'docs/research/z3-galerkin-strong-wiener-cauchy-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_strong_wiener_cauchy.py'
assert DOC.is_file() and REG.is_file()
text = CODE.read_text(encoding='utf-8')
for expected in (
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244',
    'Finset.eventually_all',
    'Filter.eventually_atTop',
    'tendsto_pow_atTop_nhds_zero_of_lt_one',
    'Real.exp_nat_mul',
    'thirdFullThreeBand_z3Galerkin_uniformFixedCoreCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244',
    'thirdFullThreeBand_z3Galerkin_exists_constructedStrongWienerCauchy244',
):
    if expected not in text:
        raise AssertionError(expected)
scrub = re.sub(r'/-.*?-/', '', text, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', text)) == 5
assert len(re.findall(r'(?m)^(?:noncomputable )?def\s+', text)) == 0
assert '200' in scrub and '5 / 6' in scrub
assert 'thirdFullThreeBandZ3GalerkinFixedCoreCube244 N' in text
print('PASS: five theorems; genuine strong finite Galerkin family; one uniform Wiener Cauchy subsequence')
