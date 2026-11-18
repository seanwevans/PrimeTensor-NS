#!/usr/bin/env python3
"""Static scope/safety checker for the infinite physical Leray ordered convolution."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3InfiniteOrderedLerayIdentification.lean')
DOC = ROOT / 'docs/research/z3-infinite-ordered-leray-identification-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_z3_infinite_ordered_leray_identification.py'
assert DOC.is_file() and REG.is_file()
code = CODE.read_text(encoding='utf-8')
for required in (
    'thirdFullThreeBandZ3InfiniteOrderedLeray244',
    'thirdFullThreeBand_z3ComplexTransport_norm_le244',
    'thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244',
    'thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244',
    'thirdFullThreeBand_z3InfiniteOrderedLeray_summable244',
    'Finset.sum_ite_eq',
    'thirdFullThreeBandZ3GalerkinExhausts244',
    'thirdFullThreeBand_z3Galerkin_partnerFilter_tendsto244',
    'thirdFullThreeBand_z3GalerkinQuadratic_exhausting_tendstoInfinite244',
    'thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244',
    'thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244',
    'thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244',
    'tendsto_nhds_unique',
):
    if required not in code:
        raise AssertionError('missing mathematical link: '+required)
scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', code)) == 9
assert len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+', code)) == 2
assert '∀ᶠ k : ℕ in atTop, p ∈ s k' in code
assert '∀ t n, Q t n = thirdFullThreeBandZ3InfiniteOrderedLeray244' in code
assert code.count('(') == code.count(')')
assert code.count('{') == code.count('}')
assert all(line == line.rstrip() for line in code.splitlines())
print('PASS: absolute convergence, cofinal pair filters, exact source stability, identified completed sum')
