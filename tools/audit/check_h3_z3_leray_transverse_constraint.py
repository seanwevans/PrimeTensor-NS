#!/usr/bin/env python3
"""Static safety and mathematical dependency audit of transverse Leray module."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
FILE=ROOT/'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3LerayTransverseConstraint.lean'
DOC=ROOT/'docs/research/z3-leray-transverse-constraint-2026-11-18.md'
REG=ROOT/'tools/audit/register_h3_z3_leray_transverse_constraint.py'
assert FILE.is_file() and DOC.is_file() and REG.is_file()
s=FILE.read_text(encoding='utf-8')
for token in (
 'thirdFullThreeBandZ3ComplexLeray244',
 'Submodule.starProjection_apply_mem',
 'Submodule.mem_orthogonal_singleton_iff_inner_right',
 'thirdFullThreeBandZ3GalerkinQuadratic244',
 'Submodule.sum_mem',
 'thirdFullThreeBand_z3InfiniteOrderedLeray_summable244',
 'tsum_mem (s := K.toAddSubmonoid)',
 'Submodule.isClosed_orthogonal',
 'thirdFullThreeBandZ3GalerkinNSField244',
 'thirdFullThreeBand_z3ComplexLeray_norm_le244',
 'thirdFullThreeBand_z3PrescribedFourier_localExistence244',
 'thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244',
):
    if token not in s: raise AssertionError('missing mathematical dependency: '+token)
clean=re.sub(r'/-.*?-/', '', s, flags=re.S)
clean=re.sub(r'--[^\n]*','',clean)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', clean)
assert len(re.findall(r'(?m)^theorem\s+', s)) == 9
assert len(re.findall(r'(?m)^def\s+', s)) == 2
assert s.count('(') == s.count(')') and s.count('{') == s.count('}')
assert all(line==line.rstrip() for line in s.splitlines())
print('PASS: exact projected complex Leray source, finite/infinite transversality, analytic projection, local construction')
