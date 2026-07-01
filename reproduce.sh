#!/usr/bin/env bash
# One-command reproduction of the data-side-capture completeness gap, refereed by SWI-Prolog.
# Prints, per query, the relational (equality) join, the unification join, and SWI-Prolog's
# answers side by side. See ADAM.md for what it means.
set -euo pipefail
cd "$(dirname "$0")"

if ! command -v swipl >/dev/null 2>&1; then
  echo "note: swipl (SWI-Prolog) is not on PATH; the independent referee column will be skipped."
  echo "      install it (e.g. 'apt install swi-prolog') to see the third column."
  echo
fi

# The join is stable Rust with zero dependencies, so a plain toolchain builds it.
exec cargo run --release --example adam_repro
