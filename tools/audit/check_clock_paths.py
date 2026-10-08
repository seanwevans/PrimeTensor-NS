#!/usr/bin/env python3
"""Check mechanical clock migration and compatibility shims against its manifest."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
manifest = json.loads((root/'docs/audit/clock-path-map.json').read_text())
legacy = {e['old_path'][:-5].replace('/', '.') for e in manifest['modules']}
for e in manifest['modules']:
    old, new = root/e['old_path'], root/e['new_path']
    src = new.read_text()
    body = ''.join(line for line in src.splitlines(keepends=True) if not line.startswith('import '))
    if hashlib.sha256(body.encode()).hexdigest() != e['implementation_body_sha256']:
        raise SystemExit(f'Implementation body changed: {e["new_path"]}')
    expected = 'import '+e['new_path'][:-5].replace('/', '.')+'\n\n/-! Compatibility import. Implementation: `'+e['new_path']+'`. -/\n'
    if old.read_text() != expected:
        raise SystemExit(f'Compatibility shim changed: {e["old_path"]}')
    for line in src.splitlines():
        if line.startswith('import ') and any(m in legacy for m in line[7:].split()):
            raise SystemExit(f'Canonical implementation imports a migrated legacy path: {e["new_path"]}')
    if len(e['new_path']) > 200 or e['new_path'].count('/') > 12:
        raise SystemExit(f'Canonical path exceeds pilot budget: {e["new_path"]}')
print(f'Clock migration: {len(manifest["modules"])} unchanged implementation bodies and compatibility shims verified.')
