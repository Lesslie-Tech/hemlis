module Review.Basic (foo) where

foo :: Int -> Int
foo x = do
  let y = x
  let unused = 1
  pure y

bar :: Int -> Int
bar z = z

-- + args: --review --json --config tests/review_fixtures/config.json
-- + expected exit status: 1
-- + expected stdout:
-- + {
-- +   "findings": [
-- +     {
-- +       "rule": "no-unused-exports",
-- +       "path": "tests/golden/review/review_json.purs",
-- +       "line": 1,
-- +       "col": 22,
-- +       "end_line": 1,
-- +       "end_col": 25,
-- +       "message": "Exported value `foo` is not used by any other module",
-- +       "fixable": false
-- +     },
-- +     {
-- +       "rule": "unqualified-do",
-- +       "path": "tests/golden/review/review_json.purs",
-- +       "line": 4,
-- +       "col": 9,
-- +       "end_line": 4,
-- +       "end_col": 11,
-- +       "message": "Unqualified `do` block; use a qualified `Module.do`",
-- +       "fixable": false
-- +     },
-- +     {
-- +       "rule": "no-unused-locals",
-- +       "path": "tests/golden/review/review_json.purs",
-- +       "line": 6,
-- +       "col": 7,
-- +       "end_line": 6,
-- +       "end_col": 13,
-- +       "message": "Local Term unused is unused",
-- +       "fixable": false
-- +     },
-- +     {
-- +       "rule": "unqualified-pure",
-- +       "path": "tests/golden/review/review_json.purs",
-- +       "line": 7,
-- +       "col": 3,
-- +       "end_line": 7,
-- +       "end_col": 7,
-- +       "message": "Unqualified `pure`; use a qualified `Applicative.pure`",
-- +       "fixable": false
-- +     },
-- +     {
-- +       "rule": "no-unused-definitions",
-- +       "path": "tests/golden/review/review_json.purs",
-- +       "line": 9,
-- +       "col": 1,
-- +       "end_line": 9,
-- +       "end_col": 4,
-- +       "message": "Definition Term bar is unused",
-- +       "fixable": false
-- +     }
-- +   ],
-- +   "suppressed": 0,
-- +   "stale_baseline_entries": 0,
-- +   "fixed": 0
-- + }

