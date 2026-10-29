#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
project_lake="${PM_ACTION_LAKE_BIN:-lake}"
"$project_lake" build
"$project_lake" env lean AuditStrict.lean
"$project_lake" env lean AuditDependencies.lean
