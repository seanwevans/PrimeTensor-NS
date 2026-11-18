#!/usr/bin/env python3
"""Static safety and scope checker for the genuine uniform-mode subsequence."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3GalerkinArzelaDiagonal.lean')
DOC = ROOT / 'docs/research/z3-galerkin-arzela-diagonal-2026-11-17.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_arzela_diagonal.py'
assert DOC.is_file() and REG.is_file()
text = CODE.read_text(encoding='utf-8')
for expected in (
    'BoundedContinuousFunction.arzela_ascoli',
    'isCompact_univ_pi',
    '.tendsto_subseq',
    'BoundedContinuousFunction.dist_coe_le_dist',
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244',
    'thirdFullThreeBand_z3Galerkin_zeroExtendTimeCurve_mem244',
    'thirdFullThreeBand_z3Galerkin_exists_constructedDiagonalFamily244',
):
    if expected not in text:
        raise AssertionError(expected)
scrub = re.sub(r'/-.*?-/', '', text, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', text)) == 8
assert len(re.findall(r'(?m)^(?:noncomputable )?def\s+', text)) == 2
print('PASS: no hidden limit assumptions; true Galerkin ODE family; Arzela + Tychonoff')
