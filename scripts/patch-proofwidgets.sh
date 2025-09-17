#!/usr/bin/env bash
set -euo pipefail

PW_LAKEFILE=".lake/packages/proofwidgets/lakefile.lean"
if [[ -f "$PW_LAKEFILE" ]]; then
  cp -f "$PW_LAKEFILE" "$PW_LAKEFILE.bak" || true
  python3 - "$PW_LAKEFILE" << 'PY'
import sys, re, pathlib
p = pathlib.Path(sys.argv[1])
s = p.read_text()
# Clear extraDepTargets in both libs
s = re.sub(r"extraDepTargets\s*:=\s*#\[[^\]]*\]", "extraDepTargets := #[]", s)
# Replace widgetJsAll targets with trivial BuildJob returning empty array
s = re.sub(r"target\s+widgetJsAll\s+pkg\s*:\s*Array FilePath\s*:=.*?(?=\n\S|\Z)",
           "target widgetJsAll pkg : Array FilePath := do\n  let dep ← inputTextFile (\"dummy\")\n  BuildJob.collectArray #[]",
           s, flags=re.S)
s = re.sub(r"target\s+widgetJsAllDev\s+pkg\s*:\s*Array FilePath\s*:=.*?(?=\n\S|\Z)",
           "target widgetJsAllDev pkg : Array FilePath := do\n  let dep ← inputTextFile (\"dummy\")\n  BuildJob.collectArray #[]",
           s, flags=re.S)
p.write_text(s)
print("Patched:", p)
PY
fi
