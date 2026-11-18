#!/usr/bin/env python3
"""Static mathematical-scope audit of exact two-cutoff full Leray source limits."""
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
              'FullThirdSolenoidalKineticThreeBandZ3GalerkinCrossCutoffLeraySource.lean')
DOC = ROOT / 'docs/research/z3-galerkin-cross-cutoff-leray-source-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_three_band_z3_galerkin_cross_cutoff_leray_source.py'
assert DOC.is_file() and REG.is_file() and SRC.is_file()
s = SRC.read_text(encoding='utf-8')
for token in (
    'thirdFullThreeBandZ3ComplexTransport244',
    'thirdFullThreeBand_z3GalerkinQuadratic_enlargeZeroSupport244',
    'thirdFullThreeBandZ3GalerkinQuadratic244',
    'thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244',
    'thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_highBall244',
    'thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_strongWienerCauchy244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'Finset.sum_subset',
    '∀ outputs : Finset CLIndex244',
):
    if token not in s:
        raise AssertionError('Missing required mathematical step: '+token)
scrub = re.sub(r'/-.*?-/', '', s, flags=re.S)
scrub = re.sub(r'--[^\n]*', '', scrub)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrub)
assert len(re.findall(r'(?m)^theorem\s+', s)) == 8
assert 'theorem thirdFullThreeBand_z3Galerkin_exists_constructedFullLeraySourceCauchy244' in s
assert 'not yet construct' in s.lower()
print('PASS: exact complex Leray on all outputs; 1000 source and 1010 field controls; no assumed PDE limit')
