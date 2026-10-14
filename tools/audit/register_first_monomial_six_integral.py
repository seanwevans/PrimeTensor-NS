#!/usr/bin/env python3
"""Register an existing, successfully checked SixIntegral module in the root build.

Run `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadSixIntegral.lean`
first. This helper intentionally does not rewrite or claim to fix the Lean source.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
module = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
    'FirstMonomialTriadSixIntegral'
)
source = ROOT / ('PrimeTensor/' + module.removeprefix('PrimeTensor.').replace('.', '/') + '.lean')
root = ROOT / 'PrimeTensor.lean'
if not source.is_file():
    raise SystemExit(f'Missing source file: {source}')
if not root.is_file():
    raise SystemExit(f'Missing root module: {root}')
import_line = 'import ' + module
lines = root.read_text().splitlines()
if import_line in lines:
    print('Already registered: ' + module)
else:
    after = ('import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.'
             'FirstMonomialTriadLowQuarterPoint3AmplitudeScaling')
    if after not in lines:
        raise SystemExit('Expected root first-monomial import anchor not found; inspect PrimeTensor.lean')
    # Append after the current root imports. Lean allows imports only before other commands.
    if any(line.strip() and not (line.startswith('import ') or line.startswith('--') or line.startswith('/-')
              or line.startswith('-/') or line.startswith('  ')) for line in lines[-10:]):
        raise SystemExit('Unexpected root module tail; inspect PrimeTensor.lean before registering')
    lines.append(import_line)
    root.write_text('\n'.join(lines).rstrip() + '\n')
    print('Registered in PrimeTensor.lean: ' + module)
