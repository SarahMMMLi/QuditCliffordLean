#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1 && [ -x .lake/toolchain/bin/lake ]; then
  PATH="$PWD/.lake/toolchain/bin:$PATH"
  export PATH
fi
lake build
lake env lean -DwarningAsError=true Audit.lean
