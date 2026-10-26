module Reach.A (entry, deadExported, exportedUnused) where

entry :: Int
entry = usedByEntry 1

usedByEntry :: Int -> Int
usedByEntry x = x

deadExported :: Int
deadExported = deadPrivate

deadPrivate :: Int
deadPrivate = 2

exportedUnused :: Int
exportedUnused = 3

privateDead :: Int
privateDead = 4
