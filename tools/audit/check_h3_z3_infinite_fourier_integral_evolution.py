#!/usr/bin/env python3
"""Static safety/math-scope check of exact Z3 Galerkin-to-infinite Fourier FTC."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3InfiniteFourierIntegralEvolution.lean')
DOC = ROOT / 'docs/research/z3-infinite-fourier-integral-evolution-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_z3_infinite_fourier_integral_evolution.py'
assert DOC.is_file() and REG.is_file()
code = CODE.read_text(encoding='utf-8')
for required in (
    'thirdFullThreeBand_z3UniformODE_FTC_limit244',
    'intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le',
    'TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn',
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244',
    'thirdFullThreeBand_z3GalerkinFiniteField_contDiff244',
    'thirdFullThreeBandZ3GalerkinExhausts244',
    'thirdFullThreeBand_z3Galerkin_limitFourierIntegralEquation244',
    'thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244',
    'thirdFullThreeBandZ3InfiniteOrderedLeray244',
    'tendsto_nhds_unique',
):
    assert required in code, 'missing core proof link: ' + required
scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', code)) == 5
assert code.count('(') == code.count(')')
assert code.count('{') == code.count('}')
assert all(line == line.rstrip() for line in code.splitlines())
assert '∀ᶠ k : ℕ in atTop, n ∈ s (phi k)' in code
assert '∀ n : EvIndex244,\n      g t n - g a n =' in code
print('PASS: exact finite derivative, uniform Bochner FTC passage, ordered infinite Fourier equation')
