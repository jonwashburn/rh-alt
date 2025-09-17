#!/usr/bin/env bash
set -euo pipefail

echo "==> Updating deps"
lake update

# Neutralize ProofWidgets JS build if present
echo "==> Patching ProofWidgets (disable widgets)"
bash scripts/patch-proofwidgets.sh || true

echo "==> Building"
lake build rh test

echo "==> Scanning for holes/axioms"
if grep -RnE '\bsorry\b|\badmit\b|^\s*axiom\b' rh | grep -v 'no sorry' ; then
  echo 'Found holes/axioms'
  exit 1
fi

echo "==> Checking theorems"
# Look for the RH wrapper and key exports
if ! grep -nE '\btheorem\s+RH\b' rh/Proof/Main.lean >/dev/null; then
  echo "Missing theorem RH in rh/Proof/Main.lean" >&2
  exit 2
fi
if ! grep -n 'no_offcritical_zeros_from_schur' rh/RS/SchurGlobalization.lean >/dev/null; then
  echo "Missing no_offcritical_zeros_from_schur in rh/RS/SchurGlobalization.lean" >&2
  exit 2
fi
if ! grep -n 'ZetaNoZerosOnRe1FromSchur' rh/RS/SchurGlobalization.lean >/dev/null; then
  echo "Missing ZetaNoZerosOnRe1FromSchur in rh/RS/SchurGlobalization.lean" >&2
  exit 2
fi
if ! grep -n 'zeta_nonzero_re_eq_one' rh/academic_framework/EulerProductMathlib.lean >/dev/null; then
  echo "Missing zeta_nonzero_re_eq_one in rh/academic_framework/EulerProductMathlib.lean" >&2
  exit 2
fi

echo "OK"
