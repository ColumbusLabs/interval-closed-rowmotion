#!/usr/bin/env bash
set -euo pipefail
exec python3 "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/portable_reproduction.py" formal "$@"
