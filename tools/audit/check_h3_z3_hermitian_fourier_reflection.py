#!/usr/bin/env python3
"""Audit exact lattice-reflection and limit-closed Hermitian data, without PDE equivariance claims."""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
                 'FullThirdSolenoidalKineticThreeBandZ3HermitianFourierReflection.lean')
DOC = ROOT / 'docs/research/z3-hermitian-fourier-reflection-2026-11-19.md'
REG = ROOT / 'tools/audit/register_h3_z3_hermitian_fourier_reflection.py'
assert SOURCE.is_file() and DOC.is_file() and REG.is_file()
s = SOURCE.read_text(encoding='utf-8')
for term in (
    'Complex.conjLIE',
    'Complex.norm_conj',
    'Complex.conjLIE.continuous',
    'PiLp.continuous_toLp',
    'thirdFullThreeBandZ3ComplexFrequency244',
    'thirdFullThreeBandZ3Degree244',
    'thirdFullThreeBandZ3Weight244',
    'thirdFullThreeBandZ3GalerkinFixedCoreCube244',
    'thirdFullThreeBand_z3FixedCoreCube_neg244',
    'thirdFullThreeBand_z3HermitianAverage_reality244',
    'thirdFullThreeBand_z3HermitianAverage_norm244',
    'thirdFullThreeBand_z3FiniteExtend_Hermitian244',
    'thirdFullThreeBand_z3Hermitian_uniformLimit244',
    'thirdFullThreeBand_z3GalerkinHermitian_uniformLimit244',
    'tendsto_nhds_unique',
):
    assert term in s, 'missing mathematics: ' + term
scrub = re.sub(r'/-.*?-/', '', s, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert s.count('theorem thirdFullThreeBand_') == 19
assert s.count('def thirdFullThreeBandZ3') == 4
for path in (SOURCE, DOC, REG):
    assert all(line == line.rstrip() for line in path.read_text().splitlines()), str(path)
assert 'not yet proved' in DOC.read_text().lower()
print('PASS: exact complex-conjugation, even spectral weights, symmetric cubes and closed Hermitian limit; nonlinear gate explicit')
