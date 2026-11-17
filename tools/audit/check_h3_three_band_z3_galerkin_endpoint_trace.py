#!/usr/bin/env python3
"""Check source contract for the cutoff-free finite Galerkin endpoint trace."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinEndpointTrace.lean'
code = SOURCE.read_text(encoding='utf-8')
scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', scrub):
    raise SystemExit('Unproved assertion in endpoint trace module')
for token in (
    'thirdFullThreeBand_z3GalerkinConstructedLocal_nonEscapeAndSpeed244',
    'thirdFullThreeBandZ3GalerkinFiniteField244',
    'Convex.norm_image_sub_le_of_norm_deriv_le',
    'LipschitzOnWith.of_dist_le_mul',
    'cauchySeq_comp',
    'cauchySeq_tendsto_of_complete',
    'le_of_tendsto',
):
    if token not in scrub: raise SystemExit('Missing proof dependency: '+token)
if re.search(r'(?m)^\s*(?:variable|axiom)\b', scrub):
    raise SystemExit('Unexpected global free variable/axiom')
print('PASS: exact Galerkin field => preterminal Lipschitz => Cauchy endpoint trace')
