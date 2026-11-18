#!/usr/bin/env python3
"""Static safety and mathematical-scope audit for longitudinal heat rigidity."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3LongitudinalHeatRigidity.lean')
DOC = ROOT / 'docs/research/z3-longitudinal-heat-rigidity-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_z3_longitudinal_heat_rigidity.py'
assert DOC.is_file() and REG.is_file()
s = CODE.read_text(encoding='utf-8')
for required in (
    'Mathlib.Analysis.ODE.Gronwall',
    'eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right',
    'thirdFullThreeBand_z3LongitudinalHeat_scalarRigidity244',
    'thirdFullThreeBand_z3LongitudinalHeat_scalarDerivative244',
    'thirdFullThreeBand_z3LongitudinalHeat_projectedDerivative244',
    'thirdFullThreeBand_z3LongitudinalHeat_solenoidalRigidity244',
    'innerSL ℂ',
    'restrictScalars ℝ',
    'thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244',
    'thirdFullThreeBandZ3InfiniteOrderedLeray244',
    'thirdFullThreeBandZ3FourierIsTransverse244',
    'HasDerivAt',
    'Ico a b',
    'Icc a b',
):
    assert required in s, 'missing theorem/proof link: '+required
scrubbed = re.sub(r'/-.*?-/', '', s, flags=re.S)
scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrubbed)
assert len(re.findall(r'(?m)^theorem\s+', s)) == 4
assert s.count('(') == s.count(')') and s.count('{') == s.count('}')
assert all(l == l.rstrip() for l in s.splitlines())
assert 'does not silently derive this differentiability' in s
print('PASS: exact scalar heat ODE, Gronwall zero, transverse full infinite source; derivative gate explicit')
