module Review.Clean (foo) where

foo :: Int -> Int
foo x = x

-- + args: --review --config tests/review_fixtures/config.json
