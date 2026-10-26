module Unused.A (foo, bar, baz_Elixir, lessThan, (<), bind, discard, Shape(..), usedByBeam, usedByScan) where

foo :: Int -> Int
foo x = x

bar :: Int -> Int
bar x = x

baz_Elixir :: Int -> Int
baz_Elixir x = x

lessThan :: Int -> Int -> Boolean
lessThan _ _ = true

infix 4 lessThan as <

bind :: forall a b. Array a -> (a -> Array b) -> Array b
bind _ _ = []

discard :: forall b. Array Int -> (Int -> Array b) -> Array b
discard _ _ = []

data Shape = Circle | Square

usedByBeam :: Int
usedByBeam = 1

usedByScan :: Int
usedByScan = 2
