module Review.Clean (foo) where

foo :: Int -> Int
foo x = x

-- + args: --review --config tests/review_fixtures/config.json
-- + expected exit status: 1
-- + expected stdout:
-- + tests/golden/review/review_clean.purs:1:22: [no-unused-exports] Exported value `foo` is not used by any other module

