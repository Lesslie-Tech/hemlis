module A where

b = 1

-- + args: --names --xx --resolve tests/golden/nr/imports_are_resolved/a.purs tests/golden/nr/imports_are_resolved/b.purs_import
-- + expected stdout:
-- + UnusedImport(Term, Ud(16993177596579750922, 'b'), Known(Fi(1), (2, 10), (2, 11)))
-- + UnusedImportUnqualified(Ud(13211085446099756707, 'A'), Known(Fi(1), (2, 0), (2, 100010)))
-- + NAMES
-- + > A
-- +    Term A b Public: ["(Known(Fi(1), (2, 10), (2, 11)), Import)", "(Known(Fi(2), (2, 0), (2, 1)), Def)"]
-- +    Module A A Public: ["(Known(Fi(1), (2, 7), (2, 8)), Ref)", "(Known(Fi(2), (0, 7), (0, 8)), Def)"]
-- + > B
-- +    Module B B Public: ["(Known(Fi(1), (0, 7), (0, 8)), Def)"]
-- + RESOLVED
-- + > A
-- +    (0, 0)->(0, 0): Module Prim Prim Public
-- +    (0, 7)->(0, 8): Module A A Public
-- +    (2, 0)->(2, 1): Term A b Public
-- + > B
-- +    (0, 0)->(0, 0): Module Prim Prim Public
-- +    (0, 7)->(0, 8): Module B B Public
-- +    (2, 7)->(2, 8): Module A A Public
-- +    (2, 10)->(2, 11): Term A b Public

