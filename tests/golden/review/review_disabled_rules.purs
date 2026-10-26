module Review.NoExports where

foo :: Int -> Int
foo x = do
  pure x

-- + args: --review --config tests/review_fixtures/config-no-do.json
-- + expected exit status: 1
-- + expected stdout:
-- + tests/golden/review/review_disabled_rules.purs:1:8: [missing-export-list] Module has no explicit export list

