#!/usr/bin/env bash
set -euo pipefail

# Disable ProofWidgets JS build by clearing extraDepTargets in its lakefile
PW_LAKEFILE=".lake/packages/proofwidgets/lakefile.lean"
if [[ -f "$PW_LAKEFILE" ]]; then
  # Backup once per run
  cp -f "$PW_LAKEFILE" "$PW_LAKEFILE.bak" || true
  # Replace extraDepTargets := #[``widgetJsAll] with extraDepTargets := #[]
  sed -E -i '' 's/extraDepTargets\s*:=\s*#\[``widgetJsAll\]/extraDepTargets := #[]/g' "$PW_LAKEFILE" || true
  sed -E -i '' 's/extraDepTargets\s*:=\s*#\[``widgetJsAll\]/extraDepTargets := #[]/g' "$PW_LAKEFILE" || true
fi
