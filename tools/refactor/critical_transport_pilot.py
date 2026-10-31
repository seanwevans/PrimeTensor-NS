#!/usr/bin/env python3
"""Pilot 2: relocate the upstream critical H³ spectral/signed-transport proof chain."""

from module_migration import main

PREFIX = (
    'PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/'
    'FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSource'
    'SpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudget'
)
H3 = 'PrimeTensor/Fluid/Vorticity/Continuation/H3/'

CONFIG = {
    'expected_head': 'bac9c73d',
    'manifest': 'docs/audit/critical-transport-path-map.json',
    'prerequisite_manifest': 'docs/audit/critical-gradient-path-map.json',
    'predecessor_line': (
        'python3 tools/refactor/critical_gradient_pilot.py --check '
        '2>&1 | tee "$report/critical-gradient-paths.log"\n'
    ),
    'check_line': (
        'python3 tools/refactor/critical_transport_pilot.py --check '
        '2>&1 | tee "$report/critical-transport-paths.log"\n'
    ),
    'pairs': [
        (PREFIX + 'SpectralEnergyGate244.lean',
         H3 + 'Critical/Spectral/EnergyGate.lean'),
        (PREFIX + 'SignedGrowthGate244.lean',
         H3 + 'Critical/Transport/SignedGrowthGate.lean'),
        (PREFIX + 'PointwiseSignedTransport244.lean',
         H3 + 'Critical/Transport/PointwiseSignedTransport.lean'),
    ],
}

if __name__ == '__main__':
    raise SystemExit(main(CONFIG))
