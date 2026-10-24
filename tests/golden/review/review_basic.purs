module Review.Basic (foo) where

foo :: Int -> Int
foo x = do
  let y = x
  let unused = 1
  pure y

bar :: Int -> Int
bar z = z

-- + args: --review --config tests/review_fixtures/config.json
-- + expected exit status: 1
-- + expected stdout:
-- + tests/golden/review/review_basic.purs:4:9: [unqualified-do] Unqualified `do` block; use a qualified `Module.do`
-- + tests/golden/review/review_basic.purs:6:7: [no-unused-locals] Local Term unused is unused
-- + tests/golden/review/review_basic.purs:7:3: [unqualified-pure] Unqualified `pure`; use a qualified `Applicative.pure`
-- + tests/golden/review/review_basic.purs:9:1: [no-unused-definitions] Definition Term bar is unused

