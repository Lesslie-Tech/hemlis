module A (module B, module Q) where

import C (eq) as Q
import C (eq, Bool, class Eq)
import B (foo)
import B (A(..), B(BA))

foo :: forall a. B

a :: B
a = AB

f x = 1

-- + args: --names --xx --resolve tests/golden/nr/unused_names_are_flagged/a.purs tests/golden/nr/unused_names_are_flagged/b.purs_import tests/golden/nr/unused_names_are_flagged/c.purs_import
-- + expected stdout:
-- + UnusedLocal(Name(Term, Ud(18086178835076887451, 'B'), Ud(4497542318236667727, 'y'), Private((10, 6))), Known(Fi(1), (10, 6), (10, 7)))
-- + UnusedLocal(Name(Term, Ud(13211085446099756707, 'A'), Ud(8312289520117458465, 'x'), Private((12, 2))), Known(Fi(0), (12, 2), (12, 3)))
-- + UnusedImport(Term, Ud(7166475107114103771, 'e'), Known(Fi(0), (3, 10), (3, 12)))
-- + UnusedImport(Type, Ud(17872905433123856768, 'B'), Known(Fi(0), (3, 14), (3, 18)))
-- + UnusedImport(Class, Ud(5069386282947683699, 'E'), Known(Fi(0), (3, 20), (3, 28)))
-- + UnusedImportUnqualified(Ud(16567872259610830857, 'C'), Known(Fi(0), (3, 0), (3, 100027)))
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(4506850079084802999, 'f'), Public), DefineSpans { name: Known(Fi(0), (7, 0), (7, 3)), sig: Some(Known(Fi(0), (7, 0), (7, 18))), body: [] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(6251214085580200729, 'f'), Public), DefineSpans { name: Known(Fi(0), (12, 0), (12, 1)), sig: Some(Known(Fi(0), (12, 0), (12, 7))), body: [] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(8186225505942432243, 'a'), Public), DefineSpans { name: Known(Fi(0), (9, 0), (9, 1)), sig: Some(Known(Fi(0), (9, 0), (9, 6))), body: [Known(Fi(0), (10, 0), (10, 6))] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(8312289520117458465, 'x'), Private((12, 2))), DefineSpans { name: Known(Fi(0), (12, 2), (12, 3)), sig: Some(Known(Fi(0), (12, 2), (12, 3))), body: [Known(Fi(0), (12, 2), (12, 7))] })
-- + UnusedLocal(Name(Term, Ud(13211085446099756707, 'A'), Ud(8312289520117458465, 'x'), Private((12, 2))), Known(Fi(3), (12, 2), (12, 3)))
-- + UnusedImport(Term, Ud(7166475107114103771, 'e'), Known(Fi(3), (3, 10), (3, 12)))
-- + UnusedImport(Type, Ud(17872905433123856768, 'B'), Known(Fi(3), (3, 14), (3, 18)))
-- + UnusedImport(Class, Ud(5069386282947683699, 'E'), Known(Fi(3), (3, 20), (3, 28)))
-- + UnusedImportUnqualified(Ud(16567872259610830857, 'C'), Known(Fi(3), (3, 0), (3, 100027)))
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(4506850079084802999, 'f'), Public), DefineSpans { name: Known(Fi(3), (7, 0), (7, 3)), sig: Some(Known(Fi(3), (7, 0), (7, 18))), body: [] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(6251214085580200729, 'f'), Public), DefineSpans { name: Known(Fi(3), (12, 0), (12, 1)), sig: Some(Known(Fi(3), (12, 0), (12, 7))), body: [] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(8186225505942432243, 'a'), Public), DefineSpans { name: Known(Fi(3), (9, 0), (9, 1)), sig: Some(Known(Fi(3), (9, 0), (9, 6))), body: [Known(Fi(3), (10, 0), (10, 6))] })
-- + UnusedDefinition(Name(Term, Ud(13211085446099756707, 'A'), Ud(8312289520117458465, 'x'), Private((12, 2))), DefineSpans { name: Known(Fi(3), (12, 2), (12, 3)), sig: Some(Known(Fi(3), (12, 2), (12, 3))), body: [Known(Fi(3), (12, 2), (12, 7))] })
-- + NAMES
-- + > <label>
-- +    Label <label> y Public: ["(Known(Fi(1), (10, 6), (10, 7)), Ref)"]
-- + > A
-- +    Type A a Private((7, 14)): ["(Known(Fi(3), (7, 14), (7, 15)), Def)"]
-- +    Term A foo Public: ["(Known(Fi(3), (7, 0), (7, 3)), Def)"]
-- +    Term A f Public: ["(Known(Fi(3), (12, 0), (12, 1)), Def)"]
-- +    Term A a Public: ["(Known(Fi(3), (9, 0), (9, 1)), Def)", "(Known(Fi(3), (10, 0), (10, 1)), Def2)"]
-- +    Term A x Private((12, 2)): ["(Known(Fi(3), (12, 2), (12, 3)), Def)"]
-- +    Module A A Public: ["(Known(Fi(3), (0, 7), (0, 8)), Def)"]
-- +    Namespace A Q Public: ["(Known(Fi(3), (0, 27), (0, 28)), Export)", "(Known(Fi(3), (2, 17), (2, 18)), Def)"]
-- + > C
-- +    Type C a Private((4, 9)): ["(Known(Fi(2), (4, 9), (4, 10)), Def)", "(Known(Fi(2), (5, 8), (5, 9)), Ref)", "(Known(Fi(2), (5, 13), (5, 14)), Ref)"]
-- +    Type C Bool Public: ["(Known(Fi(0), (3, 14), (3, 18)), Import)", "(Known(Fi(2), (0, 14), (0, 18)), Ref)", "(Known(Fi(2), (0, 14), (0, 18)), Export)", "(Known(Fi(2), (2, 5), (2, 9)), Def)", "(Known(Fi(2), (5, 18), (5, 22)), Ref)", "(Known(Fi(3), (3, 14), (3, 18)), Import)"]
-- +    Class C Eq Public: ["(Known(Fi(0), (3, 26), (3, 28)), Import)", "(Known(Fi(2), (0, 26), (0, 28)), Ref)", "(Known(Fi(2), (0, 26), (0, 28)), Export)", "(Known(Fi(2), (4, 6), (4, 8)), Def)", "(Known(Fi(3), (3, 26), (3, 28)), Import)"]
-- +    Term C eq Public: ["(Known(Fi(0), (2, 10), (2, 12)), Import)", "(Known(Fi(0), (3, 10), (3, 12)), Import)", "(Known(Fi(2), (0, 10), (0, 12)), Ref)", "(Known(Fi(2), (0, 10), (0, 12)), Export)", "(Known(Fi(2), (5, 2), (5, 4)), Def)", "(Known(Fi(3), (2, 10), (2, 12)), Import)", "(Known(Fi(3), (3, 10), (3, 12)), Import)"]
-- +    Module C C Public: ["(Known(Fi(0), (2, 7), (2, 8)), Ref)", "(Known(Fi(0), (3, 7), (3, 8)), Ref)", "(Known(Fi(2), (0, 7), (0, 8)), Def)", "(Known(Fi(3), (2, 7), (2, 8)), Ref)", "(Known(Fi(3), (3, 7), (3, 8)), Ref)"]
-- + > B
-- +    Type B A Public: ["(Known(Fi(0), (5, 10), (5, 11)), Import)", "(Known(Fi(1), (2, 5), (2, 6)), Def)", "(Known(Fi(3), (5, 10), (5, 11)), Import)"]
-- +    Type B B Public: ["(Known(Fi(0), (5, 17), (5, 18)), Import)", "(Known(Fi(0), (7, 17), (7, 18)), Ref)", "(Known(Fi(0), (9, 5), (9, 6)), Ref)", "(Known(Fi(1), (3, 5), (3, 6)), Def)", "(Known(Fi(3), (5, 17), (5, 18)), Import)", "(Known(Fi(3), (7, 17), (7, 18)), Ref)", "(Known(Fi(3), (9, 5), (9, 6)), Ref)"]
-- +    Term B AB Public: ["(Known(Fi(0), (10, 4), (10, 6)), Ref)", "(Known(Fi(1), (2, 14), (2, 16)), Def)", "(Known(Fi(3), (10, 4), (10, 6)), Ref)"]
-- +    Term B y Private((10, 6)): ["(Known(Fi(1), (10, 6), (10, 7)), Def)"]
-- +    Term B foo Public: ["(Known(Fi(0), (4, 10), (4, 13)), Import)", "(Known(Fi(1), (6, 0), (6, 3)), Def)", "(Known(Fi(1), (10, 12), (10, 15)), Ref)", "(Known(Fi(3), (4, 10), (4, 13)), Import)"]
-- +    Term B BA Public: ["(Known(Fi(0), (5, 19), (5, 21)), Import)", "(Known(Fi(1), (3, 9), (3, 11)), Def)", "(Known(Fi(3), (5, 19), (5, 21)), Import)"]
-- +    Term B AA Public: ["(Known(Fi(1), (2, 9), (2, 11)), Def)"]
-- +    Term B x Private((8, 4)): ["(Known(Fi(1), (8, 4), (8, 5)), Def)", "(Known(Fi(1), (12, 3), (12, 4)), Ref)"]
-- +    Term B _allow Private((9, 4)): ["(Known(Fi(1), (9, 4), (9, 10)), Def)"]
-- +    Term B BB Public: ["(Known(Fi(1), (3, 14), (3, 16)), Def)"]
-- +    Module B B Public: ["(Known(Fi(0), (0, 17), (0, 18)), Export)", "(Known(Fi(0), (4, 7), (4, 8)), Ref)", "(Known(Fi(0), (5, 7), (5, 8)), Ref)", "(Known(Fi(1), (0, 7), (0, 8)), Def)", "(Known(Fi(3), (0, 17), (0, 18)), Export)", "(Known(Fi(3), (4, 7), (4, 8)), Ref)", "(Known(Fi(3), (5, 7), (5, 8)), Ref)"]
-- + RESOLVED
-- + > A
-- +    (0, 0)->(0, 0): Module Prim Prim Public
-- +    (0, 7)->(0, 8): Module A A Public
-- +    (0, 17)->(0, 18): Module B B Public
-- +    (0, 27)->(0, 28): Namespace A Q Public
-- +    (2, 7)->(2, 8): Module C C Public
-- +    (2, 10)->(2, 12): Term C eq Public
-- +    (2, 17)->(2, 18): Namespace A Q Public
-- +    (3, 7)->(3, 8): Module C C Public
-- +    (3, 10)->(3, 12): Term C eq Public
-- +    (3, 14)->(3, 18): Type C Bool Public
-- +    (3, 26)->(3, 28): Class C Eq Public
-- +    (4, 7)->(4, 8): Module B B Public
-- +    (4, 10)->(4, 13): Term B foo Public
-- +    (5, 7)->(5, 8): Module B B Public
-- +    (5, 10)->(5, 11): Type B A Public
-- +    (5, 17)->(5, 18): Type B B Public
-- +    (5, 19)->(5, 21): Term B BA Public
-- +    (7, 0)->(7, 3): Term A foo Public
-- +    (7, 14)->(7, 15): Type A a Private((7, 14))
-- +    (7, 17)->(7, 18): Type B B Public
-- +    (9, 0)->(9, 1): Term A a Public
-- +    (9, 5)->(9, 6): Type B B Public
-- +    (10, 0)->(10, 1): Term A a Public
-- +    (10, 4)->(10, 6): Term B AB Public
-- +    (12, 0)->(12, 1): Term A f Public
-- +    (12, 2)->(12, 3): Term A x Private((12, 2))
-- + > C
-- +    (0, 0)->(0, 0): Module Prim Prim Public
-- +    (0, 7)->(0, 8): Module C C Public
-- +    (0, 10)->(0, 12): Term C eq Public
-- +    (0, 14)->(0, 18): Type C Bool Public
-- +    (0, 26)->(0, 28): Class C Eq Public
-- +    (2, 5)->(2, 9): Type C Bool Public
-- +    (4, 6)->(4, 8): Class C Eq Public
-- +    (4, 9)->(4, 10): Type C a Private((4, 9))
-- +    (5, 2)->(5, 4): Term C eq Public
-- +    (5, 8)->(5, 9): Type C a Private((4, 9))
-- +    (5, 13)->(5, 14): Type C a Private((4, 9))
-- +    (5, 18)->(5, 22): Type C Bool Public
-- + > B
-- +    (0, 0)->(0, 0): Module Prim Prim Public
-- +    (0, 7)->(0, 8): Module B B Public
-- +    (2, 5)->(2, 6): Type B A Public
-- +    (2, 9)->(2, 11): Term B AA Public
-- +    (2, 14)->(2, 16): Term B AB Public
-- +    (3, 5)->(3, 6): Type B B Public
-- +    (3, 9)->(3, 11): Term B BA Public
-- +    (3, 14)->(3, 16): Term B BB Public
-- +    (6, 0)->(6, 3): Term B foo Public
-- +    (8, 4)->(8, 5): Term B x Private((8, 4))
-- +    (9, 4)->(9, 10): Term B _allow Private((9, 4))
-- +    (10, 6)->(10, 7): Term B y Private((10, 6))
-- +    (10, 12)->(10, 15): Term B foo Public
-- +    (12, 3)->(12, 4): Term B x Private((8, 4))

