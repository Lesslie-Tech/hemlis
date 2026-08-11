module A where

data A = B | C | Q

newtype QQ a = QQ a

b = let { r } = 1 in { x: r }

a :: -1
a = QQ a { foo { a = a } }

readJSON :: forall @a . Array a

f = 
  let
    a@b = 1
  in
    b

-- + args: --tree --names --resolve
-- + expected stdout:
-- + UnusedLocal(Name(Term, Ud(13211085446099756707, 'A'), Ud(8186225505942432243, 'a'), Private((15, 4))), Known(Fi(0), (15, 4), (15, 5)))
-- + TREE: A
-- + Module
-- +  Header
-- +   MName
-- +    (0, 7)->(0, 8)
-- +   NULL
-- +   (0, 0)->(0, 6)
-- +   (0, 9)->(0, 14)
-- +   Decl::Data
-- +    ProperName
-- +     (2, 5)->(2, 6)
-- +     (
-- +      ProperName
-- +       (2, 9)->(2, 10)
-- +     )
-- +     (
-- +      ProperName
-- +       (2, 13)->(2, 14)
-- +     )
-- +     (
-- +      ProperName
-- +       (2, 17)->(2, 18)
-- +     )
-- +   Decl::NewType
-- +    ProperName
-- +     (4, 8)->(4, 10)
-- +     TypVarBinding
-- +      Name
-- +       (4, 11)->(4, 12)
-- +      NULL
-- +    ProperName
-- +     (4, 15)->(4, 17)
-- +    Typ::Var
-- +     Name
-- +      (4, 18)->(4, 19)
-- +   Decl::Def
-- +    Name
-- +     (6, 0)->(6, 1)
-- +    GuardedExpr::Unconditional
-- +     Expr::Let
-- +      (6, 4)->(6, 7)
-- +       LetBinding::Pattern
-- +        Binder::Record
-- +          RecordLabelBinder::Pun
-- +           Name
-- +            (6, 10)->(6, 11)
-- +        Expr::Number
-- +         Number
-- +          (6, 16)->(6, 17)
-- +      Expr::Record
-- +       (6, 21)->(6, 22)
-- +        RecordLabelExpr::Field
-- +         Label
-- +          (6, 23)->(6, 24)
-- +         Expr::Ident
-- +          QName
-- +           NULL
-- +           Name
-- +            (6, 26)->(6, 27)
-- +       (6, 28)->(6, 29)
-- +   Decl::Sig
-- +    Name
-- +     (8, 0)->(8, 1)
-- +    Typ::Int
-- +     Int
-- +      (8, 5)->(8, 6)
-- +   Decl::Def
-- +    Name
-- +     (9, 0)->(9, 1)
-- +    GuardedExpr::Unconditional
-- +     Expr::App
-- +      Expr::Constructor
-- +       QProperName
-- +        NULL
-- +        ProperName
-- +         (9, 4)->(9, 6)
-- +      Expr::Update
-- +       Expr::Ident
-- +        QName
-- +         NULL
-- +         Name
-- +          (9, 7)->(9, 8)
-- +       (9, 9)->(9, 10)
-- +        RecordUpdate::Branch
-- +         Label
-- +          (9, 11)->(9, 14)
-- +          RecordUpdate::Leaf
-- +           Label
-- +            (9, 17)->(9, 18)
-- +           Expr::Ident
-- +            QName
-- +             NULL
-- +             Name
-- +              (9, 21)->(9, 22)
-- +       (9, 25)->(9, 26)
-- +   Decl::Sig
-- +    Name
-- +     (11, 0)->(11, 8)
-- +    Typ::Forall
-- +      TypVarBinding
-- +       Name
-- +        (11, 20)->(11, 21)
-- +       NULL
-- +     Typ::App
-- +      Typ::Constructor
-- +       QProperName
-- +        NULL
-- +        ProperName
-- +         (11, 24)->(11, 29)
-- +      Typ::Var
-- +       Name
-- +        (11, 30)->(11, 31)
-- +   Decl::Def
-- +    Name
-- +     (13, 0)->(13, 1)
-- +    GuardedExpr::Unconditional
-- +     Expr::Let
-- +      (14, 2)->(14, 5)
-- +       LetBinding::Pattern
-- +        Binder::Named
-- +         Name
-- +          (15, 4)->(15, 5)
-- +         Binder::Var
-- +          Name
-- +           (15, 6)->(15, 7)
-- +        Expr::Number
-- +         Number
-- +          (15, 10)->(15, 11)
-- +      Expr::Ident
-- +       QName
-- +        NULL
-- +        Name
-- +         (17, 4)->(17, 5)
-- + 
-- + NAMES
-- + > <label>
-- +    Label <label> x Public: ["(Known(Fi(0), (6, 23), (6, 24)), Ref)"]
-- +    Label <label> r Public: ["(Known(Fi(0), (6, 10), (6, 11)), Ref)"]
-- + > A
-- +    Type A a Private((4, 11)): ["(Known(Fi(0), (4, 11), (4, 12)), Def)", "(Known(Fi(0), (4, 18), (4, 19)), Ref)"]
-- +    Type A a Private((11, 20)): ["(Known(Fi(0), (11, 20), (11, 21)), Def)", "(Known(Fi(0), (11, 30), (11, 31)), Ref)"]
-- +    Type A A Public: ["(Known(Fi(0), (2, 5), (2, 6)), Def)"]
-- +    Type A QQ Public: ["(Known(Fi(0), (4, 8), (4, 10)), Def)"]
-- +    Term A Q Public: ["(Known(Fi(0), (2, 17), (2, 18)), Def)"]
-- +    Term A readJSON Public: ["(Known(Fi(0), (11, 0), (11, 8)), Def)"]
-- +    Term A f Public: ["(Known(Fi(0), (13, 0), (13, 1)), Def)"]
-- +    Term A a Private((15, 4)): ["(Known(Fi(0), (15, 4), (15, 5)), Def)"]
-- +    Term A a Public: ["(Known(Fi(0), (8, 0), (8, 1)), Def)", "(Known(Fi(0), (9, 0), (9, 1)), Def2)", "(Known(Fi(0), (9, 7), (9, 8)), Ref)", "(Known(Fi(0), (9, 21), (9, 22)), Ref)"]
-- +    Term A r Private((6, 10)): ["(Known(Fi(0), (6, 10), (6, 11)), Def)", "(Known(Fi(0), (6, 26), (6, 27)), Ref)"]
-- +    Term A C Public: ["(Known(Fi(0), (2, 13), (2, 14)), Def)"]
-- +    Term A QQ Public: ["(Known(Fi(0), (4, 15), (4, 17)), Def)", "(Known(Fi(0), (9, 4), (9, 6)), Ref)"]
-- +    Term A b Private((15, 6)): ["(Known(Fi(0), (15, 6), (15, 7)), Def)", "(Known(Fi(0), (17, 4), (17, 5)), Ref)"]
-- +    Term A b Public: ["(Known(Fi(0), (6, 0), (6, 1)), Def)"]
-- +    Term A B Public: ["(Known(Fi(0), (2, 9), (2, 10)), Def)"]
-- +    Module A A Public: ["(Known(Fi(0), (0, 7), (0, 8)), Def)"]

