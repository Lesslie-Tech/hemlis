module T where

f =
  case 1 of
    SEK ->
      let
        a = b (-1.0) c
      in
      1

    _ -> 1

f =
  case 1 of
    3 -> baz
      where
      baz = 3

