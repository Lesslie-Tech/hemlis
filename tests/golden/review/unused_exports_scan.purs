module Unused.B (main, compare) where

import Unused.A as A

main :: Array Int
main = A.do
  x <- [A.foo 1]
  [x]

compare :: Boolean
compare = 1 A.< 2

-- + args: --review --json --rule no-unused-exports --config tests/review_fixtures/unused-scan.json tests/review_fixtures/unused/A.purs
-- + expected exit status: 1
-- + expected stdout:
-- + {
-- +   "findings": [
-- +     {
-- +       "rule": "no-unused-exports",
-- +       "path": "tests/golden/review/unused_exports_scan.purs",
-- +       "line": 1,
-- +       "col": 24,
-- +       "end_line": 1,
-- +       "end_col": 31,
-- +       "message": "Exported value `compare` is not used by any other module"
-- +     },
-- +     {
-- +       "rule": "no-unused-exports",
-- +       "path": "unused/A.purs",
-- +       "line": 1,
-- +       "col": 81,
-- +       "end_line": 1,
-- +       "end_col": 91,
-- +       "message": "Exported value `usedByBeam` is not used by any other module"
-- +     }
-- +   ],
-- +   "suppressed": 0,
-- +   "stale_baseline_entries": 0
-- + }

