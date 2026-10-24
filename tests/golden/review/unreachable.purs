module Reach.B (deadInB) where

import Reach.A as A

deadInB :: Int
deadInB = A.deadExported

-- + args: --review --rule no-unreachable-definitions --rule no-unused-modules --config tests/review_fixtures/reach.json tests/review_fixtures/reach/A.purs
-- + expected exit status: 1
-- + expected stdout:
-- + tests/review_fixtures/reach/A.purs:9:1: [no-unreachable-definitions] Value `deadExported` is not reachable from any entry point, nor is anything that uses it
-- + tests/review_fixtures/reach/A.purs:12:1: [no-unreachable-definitions] Value `deadPrivate` is not reachable from any entry point
-- + tests/review_fixtures/reach/A.purs:15:1: [no-unreachable-definitions] Value `exportedUnused` is not reachable from any entry point, nor is anything that uses it
-- + tests/review_fixtures/reach/A.purs:18:1: [no-unreachable-definitions] Value `privateDead` is not reachable from any entry point
-- + tests/golden/review/unreachable.purs:1:8: [no-unused-modules] Module `Reach.B` has no definition reachable from any entry point
-- + tests/golden/review/unreachable.purs:5:1: [no-unreachable-definitions] Value `deadInB` is not reachable from any entry point, nor is anything that uses it

