module Review.Basic (foo) where

foo :: Int -> Int
foo x = do
  let y = x
  let unused = 1
  pure y

bar :: Int -> Int
bar z = z

-- + args: --review --rule unqualified-do --config tests/review_fixtures/config.json
-- + expected exit status: 1
-- + expected stdout:
-- + tests/golden/review/review_rule_filter.purs:4:9: [unqualified-do] Unqualified `do` block; use a qualified `Module.do`

