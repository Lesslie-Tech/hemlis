module Unused.B (main, compare) where

import Unused.A as A

main :: Array Int
main = A.do
  x <- [A.foo 1]
  [x]

compare :: Boolean
compare = 1 A.< 2

-- + args: --review --rule no-unused-exports --config tests/review_fixtures/unused.json --beam-edges tests/review_fixtures/unused/edges.txt tests/review_fixtures/unused/A.purs
-- + expected exit status: 1
-- + expected stdout:
-- + tests/golden/review/unused_exports_beam.purs:1:24: [no-unused-exports] Exported value `compare` is not used by any other module
-- + tests/review_fixtures/unused/A.purs:1:23: [no-unused-exports] Exported value `bar` is not used by any other module
-- + tests/review_fixtures/unused/A.purs:1:93: [no-unused-exports] Exported value `usedByScan` is not used by any other module

