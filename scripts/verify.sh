#!/usr/bin/env bash
# Compile the proof library and all public proof bindings, then audit every owned declaration.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-repository.py
lake build
lake env lean -Dbackward.isDefEq.respectTransparency=false scripts/axiom-audit.lean
