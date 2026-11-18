#!/usr/bin/env python3
"""Static scope and interface audit for prescribed-data Z3 Fourier existence."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3PrescribedFourierLocalExistence.lean')
DOC = ROOT / 'docs/research/z3-prescribed-fourier-local-existence-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_z3_prescribed_fourier_local_existence.py'
assert DOC.is_file() and REG.is_file() and CODE.is_file()
code = CODE.read_text(encoding='utf-8')
for link in (
    'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244',
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244',
    'thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244',
    'thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244',
    'thirdFullThreeBand_z3PrescribedInitial_finiteProjectionStrict244',
    'thirdFullThreeBand_z3UniformSourceCauchy_pointwiseUniform244',
    'thirdFullThreeBand_z3GalerkinExhausts_subsequence244',
    'thirdFullThreeBand_z3GalerkinFixedCubes_exhaust244',
    'thirdFullThreeBand_z3PrescribedFourier_localExistence244',
    'hInitialTrace',
    'hExhaustPhi',
    'hEquation',
    'tendsto_nhds_unique',
):
    assert link in code, 'missing mathematical dependency: ' + link
stripped = re.sub(r'/-.*?-/', '', code, flags=re.S)
stripped = re.sub(r'--[^\n]*', '', stripped)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', stripped)
assert len(re.findall(r'(?m)^theorem\s+', code)) == 5
assert 'thirdFullThreeBandZ3GalerkinExhausts244 s' in code
assert 'thirdFullThreeBandZ3InfiniteWienerMass244\n      (Real.log (2 : ℝ)) u0 < 100' in code
assert 'g t n - u0 n =' in code
assert code.count('(') == code.count(')')
assert code.count('{') == code.count('}')
assert all(line == line.rstrip() for line in code.splitlines())
print('PASS: prescribed initial restriction, one diagonal, complete Leray source and infinite FTC')
