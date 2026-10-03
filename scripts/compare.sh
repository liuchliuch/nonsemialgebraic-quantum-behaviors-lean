#!/usr/bin/env bash
# Use Landrun by default, or explicitly select an unsandboxed development run.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:-}"
if [[ "$mode" != "" && "$mode" != "--local" ]]; then
  echo "Usage: bash scripts/compare.sh [--local]" >&2
  exit 2
fi
location="${COMPARATOR_HOME:-$PWD/.verification/tools/comparator}"
export PATH="$location/.lake/build/bin:$location/.lake/packages/lean4export/.lake/build/bin:$PATH"
if [[ "$mode" == "--local" ]]; then
  echo "Local Comparator mode: statement comparison, axiom checks, and kernel replay; no OS sandbox."
  runner_dir="$(mktemp -d)"
  trap 'rm -rf "$runner_dir"' EXIT
  cat > "$runner_dir/landrun" <<'RUNNER'
#!/usr/bin/env bash
set -euo pipefail
while (($#)); do
  case "$1" in
    --best-effort|-ldd|-add-exec) shift ;;
    --ro|--rw|--rwx|--rox|--env) shift 2 ;;
    lake|lean4export) exec "$@" ;;
    *) echo "Unsupported development-runner argument: $1" >&2; exit 2 ;;
  esac
done
exit 2
RUNNER
  chmod +x "$runner_dir/landrun"
  export PATH="$runner_dir:$PATH"
fi
for tool in comparator lean4export landrun; do
  command -v "$tool" >/dev/null || { echo "Missing $tool; see docs/verification.md" >&2; exit 1; }
done
lake env comparator Verification/comparator.json
