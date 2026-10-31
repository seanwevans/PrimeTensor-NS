#!/usr/bin/env python3
"""Pilot 3: four critical annular geometry / all-orders radial-energy proof steps."""

from module_migration import main

PREFIX = (
    'PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudget'
)
H3 = 'PrimeTensor/Fluid/Vorticity/Continuation/H3/'

CONFIG = {
    'expected_head': '6b95cba1',
    'manifest': 'docs/audit/critical-radial-path-map.json',
    'prerequisite_manifest': 'docs/audit/critical-transport-path-map.json',
    'predecessor_line': (
        'python3 tools/refactor/critical_transport_pilot.py --check '
        '2>&1 | tee "$report/critical-transport-paths.log"\n'
    ),
    'check_line': (
        'python3 tools/refactor/critical_radial_pilot.py --check '
        '2>&1 | tee "$report/critical-radial-paths.log"\n'
    ),
    'pairs': [
        (PREFIX + 'EnergyOuterGeometry244.lean',
         H3 + 'Critical/AnnularGeometry/EnergyOuter.lean'),
        (PREFIX + 'SecondMomentCriticalEnergy244.lean',
         H3 + 'Critical/RadialMoments/SecondMomentEnergy.lean'),
        (PREFIX + 'SharpFourthEnergy244.lean',
         H3 + 'Critical/RadialMoments/SharpFourthEnergy.lean'),
        (PREFIX + 'AllOrdersSharpEnergy244.lean',
         H3 + 'Critical/RadialMoments/AllOrdersSharpEnergy.lean'),
    ],
    # A previously migrated canonical consumer currently uses the long historical
    # AllOrdersSharpEnergy import. Move that direct edge to the actual implementation.
    # Its proof body remains byte-identical; update its prior manifest's import list
    # so Pilot 2's independent checker continues to attest the new canonical graph.
    'consumer_rewrites': [
        {
            'path': H3 + 'Critical/Spectral/EnergyGate.lean',
            'previous_manifest': 'docs/audit/critical-transport-path-map.json',
            'legacy_module': (PREFIX + 'AllOrdersSharpEnergy244.lean')[:-5].replace('/', '.'),
            'canonical_module': (H3 + 'Critical/RadialMoments/AllOrdersSharpEnergy.lean')[:-5].replace('/', '.'),
        },
    ],
}

if __name__ == '__main__':
    raise SystemExit(main(CONFIG))
