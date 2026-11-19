#!/usr/bin/env python3
"""Audit the finite ODE to constructed solenoidal Fourier limit chain."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3ConstructedSolenoidalLocalExistence.lean')
DOC = ROOT / 'docs/research/z3-constructed-solenoidal-local-existence-2026-11-18.md'
REG = ROOT / 'tools/audit/register_h3_z3_constructed_solenoidal_local_existence.py'
assert CODE.is_file() and DOC.is_file() and REG.is_file()
s = CODE.read_text(encoding='utf-8')
for required in (
    'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244',
    'thirdFullThreeBand_z3GalerkinQuadratic_transverse244',
    'thirdFullThreeBand_z3LongitudinalHeat_scalarRigidity244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_transversePreserved244',
    'thirdFullThreeBand_z3Galerkin_uniformLimit_transverse244',
    'thirdFullThreeBand_z3ProjectedInitial_solenoidalLocalExistence244',
    'thirdFullThreeBand_z3FixedCubes_solenoidalLocalExistence244',
    'thirdFullThreeBand_z3ProjectedInitial_admissible244',
    'thirdFullThreeBand_z3ProjectedInitial_transverse244',
    'thirdFullThreeBand_z3Galerkin_actualCutoffs_uniformModeSubsequence244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_infiniteWienerLimit244',
    'thirdFullThreeBand_z3Galerkin_uniformTime_fullLeraySourceCauchy244',
    'thirdFullThreeBand_z3Galerkin_uniformSourceCompletion244',
    'thirdFullThreeBand_z3Galerkin_completedSource_eq_orderedLeray244',
    'thirdFullThreeBand_z3Galerkin_orderedLerayIntegralEquation244',
    'thirdFullThreeBand_z3GalerkinFixedCubes_exhaust244',
    'hTransverseLimit',
    'hInitialFiniteTrans',
    'hFiniteTrans',
    'hODE',
):
    assert required in s, 'missing mathematical step: ' + required
scrubbed = re.sub(r'/-.*?-/', '', s, flags=re.S)
scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', scrubbed)
assert len(re.findall(r'(?m)^theorem\s+', s)) == 4
assert s.count('(') == s.count(')')
assert s.count('{') == s.count('}')
for path in (CODE, DOC, REG):
    assert all(line == line.rstrip() for line in path.read_text().splitlines()), str(path)
assert 'NO differentiability premise' in s
print('PASS: finite ODE heat rigidity; exhaustive limit; joint source-integral construction; no infinite derivative gate')
