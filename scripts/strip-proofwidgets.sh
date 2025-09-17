#!/usr/bin/env bash
set -euo pipefail

strip_manifest() {
  local f="$1"
  [[ -f "$f" ]] || return 0
  python3 - "$f" << 'PY'
import sys, json, pathlib
p = pathlib.Path(sys.argv[1])
try:
  j = json.loads(p.read_text())
except Exception:
  sys.exit(0)
if isinstance(j, dict) and 'packages' in j and isinstance(j['packages'], list):
  before = len(j['packages'])
  j['packages'] = [pkg for pkg in j['packages'] if pkg.get('name') != 'proofwidgets']
  after = len(j['packages'])
  if after != before:
    p.write_text(json.dumps(j, indent=2))
    print(f"Stripped proofwidgets from {p}")
PY
}

strip_manifest "lake-manifest.json"
strip_manifest "meta-proof/lake-manifest.json" || true
