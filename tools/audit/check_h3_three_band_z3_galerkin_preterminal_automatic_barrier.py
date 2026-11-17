#!/usr/bin/env python3
"""Static source audit for automatic finite Galerkin preterminal nonescape."""
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / ('PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/'
               'FullThirdSolenoidalKineticThreeBandZ3GalerkinPreterminalAutomaticBarrier.lean')
code = FILE.read_text(encoding='utf-8')
clean = re.sub(r'/-.*?-/', '', code, flags=re.S)
clean = re.sub(r'--[^\n]*', '', clean)
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', clean), 'unproved term'
assert all(line == line.rstrip() for line in code.splitlines()), 'trailing space'
checks = {
    'thirdFullThreeBand_z3GalerkinFiniteWienerMass_continuous244':
        ('continuous_finsetSum', 'continuous_apply'),
    'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticMovingBall244':
        ('thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244',
         'thirdFullThreeBand_z3GalerkinFiniteODE_coordinate_hasDerivAt244'),
    'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticNonEscape244':
        ('thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244',),
    'thirdFullThreeBand_z3GalerkinFiniteODE_endpointDistance51000_244':
        ('le_of_tendsto_of_tendsto',),
    'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalAutomaticEndpoint244':
        ('thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_nonescape244',
         'hEndHigh', 'hTimesEnd'),
}
for name, markers in checks.items():
    pattern = r'(?m)^theorem\s+' + re.escape(name) + r'\b'
    assert len(re.findall(pattern, clean)) == 1, f'bad theorem declaration {name}'
    for marker in markers:
        assert marker in clean, f'missing {marker}'
assert 'hInitial' in clean and 'hODE' in clean and 'hWindow' in clean
print(f'PASS: source audit: {len(checks)} preterminal automatic barrier theorems')
print('NOTE: static audit is not Lean compilation and cannot certify a proof')
