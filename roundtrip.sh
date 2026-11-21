#!/bin/bash
# No arguments checks every repository .agda module, including historical fixtures.
set -euo pipefail
cd "$(dirname "$0")"
exec python3 scripts/verify_modules.py roundtrip "$@"
