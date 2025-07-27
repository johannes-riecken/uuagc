{-# LANGUAGE OverloadedStrings #-}
import TigerASS
import Test.Hspec
import Prettyprinter

main :: IO ()
-- main = print . pretty $ p1
main = do
    p1_pretty <- readFile "../testcases_pprint/test_patch.tig"
    p2_pretty <- readFile "../testcases_pprint/test.tig"
    p3_pretty <- readFile "../testcases_pprint/test12.tig"
    p4_pretty <- readFile "../testcases_pprint/test39.tig"
    p5_pretty <- readFile "../testcases_pprint/test4.tig"
    hspec $ do
        describe "p1" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p1) `shouldBe` p1_pretty
        describe "p2" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p2) `shouldBe` p2_pretty
        describe "p3" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p3) `shouldBe` p3_pretty
        describe "p4" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p2) `shouldBe` p2_pretty
        describe "p5" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p2) `shouldBe` p2_pretty

instance Pretty Program where
    pretty (Program e) = pretty e

instance Pretty Ident where
    pretty (Id x) = pretty x

sw = 4

instance Pretty Expr where
    pretty (LValue x) = pretty x
    pretty (Apply v args) = pretty v <> parens (foldr1 (surround ", ") . map pretty $ args)
    pretty (For v e0 e1 e2) = "for" <+> pretty v <+> ":=" <+> pretty e0 <+> "to" <+> pretty e1 <+> "do" <+> pretty e2
    -- Is that a bug in the parser?
    pretty (Op x@"<" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@">" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x l r) = pretty l <+> pretty x <+> pretty r
    pretty (If e0 e1 e2) = nest sw . vsep $ ["if" <+> pretty e0, "then" <+> pretty e1, "else" <+> pretty e2]
    pretty (Let ds e) = vsep ["let", indent sw . vsep . map pretty $ ds, "in", indent sw . pretty $ e, "end"]
    pretty (Assign v e) = pretty v <+> ":=" <+> pretty e
    pretty (IntLit x) = pretty x
    pretty Skip = "()"
    pretty x@(Sequence e0 e1) = parens $ prettySeq x
    pretty x = error ("missing pretty: " <> show x)

prettySeq (Sequence e0 e1@(Sequence _ _)) = pretty e0 <> ";" <+> prettySeq e1
prettySeq (Sequence e0 e1) = pretty e0 <> ";" <+> pretty e1

instance Pretty FunDec where
    pretty (FunDec nm args Nothing body) = vsep ["function" <+> pretty nm <> parens (foldr1 (surround ", ") $ map pretty args) <+> "=", pretty body]
    pretty (FunDec nm args (Just ret) body) = nest sw $ vsep ["function" <+> pretty nm <> parens (foldr1 (surround ", ") $ map pretty args) <+> ":" <+> pretty ret <+> "=", pretty body]

instance Pretty DeclGroup where
    pretty (VarDec x Nothing e) = "var" <+> pretty x <+> ":=" <+> pretty e
    pretty (FunDecs x) = vsep . map pretty $ x
    pretty x = error ("missing pretty: " <> show x)

instance Pretty LValue where
    pretty (Ident x) = pretty x

instance Pretty TypedVar where
    pretty (TypedVar v t) = pretty v <+> ":" <+> pretty t
-- data Expr = LValue (LValue)
--           | Apply (VarIdent) (Args)
--           | RecordVal (TypeIdent) (AssignFields)
--           | ArrayVal (TypeIdent) (Expr) (Expr)
--           | IntLit (Integer)
--           | StringLit (String)
--           | While (Expr) (Expr)
--           | For (VarIdent) (Expr) (Expr) (Expr)
--           | If (Expr) (Expr) (Expr)
--           | Let (Declarations) (Expr)
--           | Assign (LValue) (Expr)
--           | Op (String) (Expr) (Expr)
--           | UnOp (String) (Expr)
--           | Skip
--           | Nil
--           | Break
--           | Sequence (Expr) (Expr)

-- ../testcases_pprint/test_patch.ast
p1 = Program
  (Let
     [FunDecs
        [FunDec
           "g"
           [TypedVar "a" "int",
            TypedVar "b" "int",
            TypedVar "c" "int",
            TypedVar "d" "int"]
           (Just "int")
           (If
              (Op
                 "|"
                 (Op ">" (LValue (Ident "b")) (LValue (Ident "a")))
                 (Op "<" (LValue (Ident "d")) (LValue (Ident "c"))))
              (Op "+" (LValue (Ident "a")) (LValue (Ident "d")))
              (Op "+" (LValue (Ident "c")) (LValue (Ident "b"))))]]
     (Apply
        "printi"
        [Apply
           "g" [IntLit 9, IntLit 4, IntLit 3, IntLit 2]]))

-- ../testcases_pprint/test.ast
p2 = Program
  (Let
     [FunDecs
        [FunDec
           "sum"
           [TypedVar "v1" "int",
            TypedVar "v2" "int",
            TypedVar "v3" "int",
            TypedVar "v4" "int",
            TypedVar "v5" "int",
            TypedVar "v6" "int",
            TypedVar "v7" "int"]
           (Just "int")
           (Let
              [VarDec
                 "sum"
                 Nothing
                 (Op
                    "+"
                    (Op
                       "+"
                       (Op
                          "+"
                          (Op
                             "+"
                             (Op
                                "+"
                                (Op
                                   "+"
                                   (LValue (Ident "v1"))
                                   (LValue (Ident "v2")))
                                (LValue (Ident "v3")))
                             (LValue (Ident "v4")))
                          (LValue (Ident "v5")))
                       (LValue (Ident "v6")))
                    (LValue (Ident "v7")))]
              (LValue (Ident "sum")))]]
     (Apply
        "printi"
        [Apply
           "sum"
           [IntLit 1,
            IntLit 2,
            IntLit 3,
            IntLit 4,
            IntLit 5,
            IntLit 6,
            IntLit 7]]))

-- ../testcases_pprint/test12.ast
p3 = Program
  (Let
     [VarDec "a" Nothing (IntLit 0)]
     (For
        "i"
        (IntLit 0)
        (IntLit 100)
        (Sequence
           (Assign
              (Ident "a") (Op "+" (LValue (Ident "a")) (IntLit 1)))
           Skip)))

-- ../testcases_pprint/test39.ast
p4 = Program
  (Let
     [FunDecs
        [FunDec
           "g0"
           [TypedVar "a" "int"]
           (Just "int")
           (LValue (Ident "a")),
         FunDec
           "g1"
           [TypedVar "a" "int"]
           (Just "int")
           (LValue (Ident "a"))]]
     (IntLit 0))

-- ../testcases_pprint/test4.ast
p5 = Program
  (Let
     [FunDecs
        [FunDec
           "nfactor"
           [TypedVar "n" "int"]
           (Just "int")
           (If
              (Op "=" (IntLit 0) (LValue (Ident "n")))
              (IntLit 1)
              (Op
                 "*"
                 (LValue (Ident "n"))
                 (Apply
                    "nfactor"
                    [Op "-" (LValue (Ident "n")) (IntLit 1)])))]]
     (Apply "nfactor" [IntLit 10]))
