{-# LANGUAGE OverloadedStrings #-}
module PprintTests where
import TigerASS
import Test.Hspec
import Prettyprinter
import Hedgehog
import TigerPretty

-- prop_tripping :: Property
-- prop_tripping =
--     property $ do
--         j

main :: IO ()
-- main = print . pretty $ p1
main = do
    -- checkParallel $ Group "Test.Example" [
    --     ("prop_tripping", prop_tripping)
    --     ]
    p1_pretty <- readFile "../testcases_pprint/test_patch.tig"
    p2_pretty <- readFile "../testcases_pprint/test.tig"
    p3_pretty <- readFile "../testcases_pprint/test12.tig"
    p4_pretty <- readFile "../testcases_pprint/test39.tig"
    p5_pretty <- readFile "../testcases_pprint/test4.tig"
    p6_pretty <- readFile "../testcases_pprint/merge.tig"
    p7_pretty <- readFile "../testcases_pprint/queens.tig"
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
                ((<> "\n") . show . pretty $ p4) `shouldBe` p4_pretty
        describe "p5" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p5) `shouldBe` p5_pretty
        describe "p6" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p6) `shouldBe` p6_pretty
        describe "p7" $ do
            it "rewrites" $ do
                ((<> "\n") . show . pretty $ p7) `shouldBe` p7_pretty
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

-- ../testcases_pprint/merge.ast
p6 = Program (Let [TypeDecs [TypeDec "any" (Record [TypedVar "any" "int"])],VarDec "buffer" Nothing (Apply "getchar" []),FunDecs [FunDec "readint" [TypedVar "any" "any"] (Just "int") (Let [VarDec "i" Nothing (IntLit 0),FunDecs [FunDec "isdigit" [TypedVar "s" "string"] (Just "int") (Op "&" (Op ">=" (Apply "ord" [StringLit "\"0\""]) (Apply "ord" [LValue (Ident "buffer")])) (Op "<=" (Apply "ord" [StringLit "\"9\""]) (Apply "ord" [LValue (Ident "buffer")]))),FunDec "skipto" [] Nothing (While (Op "|" (Op "=" (StringLit "\" \"") (LValue (Ident "buffer"))) (Op "=" (StringLit "\"\\n\"") (LValue (Ident "buffer")))) (Assign (Ident "buffer") (Apply "getchar" [])))]] (Sequence (Apply "skipto" []) (Sequence (Assign (Dot (Ident "any") "any") (Apply "isdigit" [LValue (Ident "buffer")])) (Sequence (While (Apply "isdigit" [LValue (Ident "buffer")]) (Sequence (Assign (Ident "i") (Op "-" (Op "+" (Op "*" (LValue (Ident "i")) (IntLit 10)) (Apply "ord" [LValue (Ident "buffer")])) (Apply "ord" [StringLit "\"0\""]))) (Assign (Ident "buffer") (Apply "getchar" [])))) (LValue (Ident "i"))))))],TypeDecs [TypeDec "list" (Record [TypedVar "first" "int",TypedVar "rest" "list"])],FunDecs [FunDec "readlist" [] (Just "list") (Let [VarDec "any" Nothing (RecordVal "any" [AssignField "any" (IntLit 0)]),VarDec "i" Nothing (Apply "readint" [LValue (Ident "any")])] (If (LValue (Dot (Ident "any") "any")) (RecordVal "list" [AssignField "first" (LValue (Ident "i")),AssignField "rest" (Apply "readlist" [])]) Nil)),FunDec "merge" [TypedVar "a" "list",TypedVar "b" "list"] (Just "list") (If (Op "=" Nil (LValue (Ident "a"))) (LValue (Ident "b")) (If (Op "=" Nil (LValue (Ident "b"))) (LValue (Ident "a")) (If (Op "<" (LValue (Dot (Ident "b") "first")) (LValue (Dot (Ident "a") "first"))) (RecordVal "list" [AssignField "first" (LValue (Dot (Ident "a") "first")),AssignField "rest" (Apply "merge" [LValue (Dot (Ident "a") "rest"),LValue (Ident "b")])]) (RecordVal "list" [AssignField "first" (LValue (Dot (Ident "b") "first")),AssignField "rest" (Apply "merge" [LValue (Ident "a"),LValue (Dot (Ident "b") "rest")])])))),FunDec "printint" [TypedVar "i" "int"] Nothing (Let [FunDecs [FunDec "f" [TypedVar "i" "int"] Nothing (If (Op ">" (IntLit 0) (LValue (Ident "i"))) (Sequence (Apply "f" [Op "/" (LValue (Ident "i")) (IntLit 10)]) (Apply "print" [Apply "chr" [Op "+" (Op "-" (LValue (Ident "i")) (Op "*" (Op "/" (LValue (Ident "i")) (IntLit 10)) (IntLit 10))) (Apply "ord" [StringLit "\"0\""])]])) Skip)]] (If (Op "<" (IntLit 0) (LValue (Ident "i"))) (Sequence (Apply "print" [StringLit "\"-\""]) (Apply "f" [UnOp "-" (LValue (Ident "i"))])) (If (Op ">" (IntLit 0) (LValue (Ident "i"))) (Apply "f" [LValue (Ident "i")]) (Apply "print" [StringLit "\"0\""])))),FunDec "printlist" [TypedVar "l" "list"] Nothing (If (Op "=" Nil (LValue (Ident "l"))) (Apply "print" [StringLit "\"\\n\""]) (Sequence (Apply "printint" [LValue (Dot (Ident "l") "first")]) (Sequence (Apply "print" [StringLit "\" \""]) (Apply "printlist" [LValue (Dot (Ident "l") "rest")]))))],VarDec "list1" Nothing (Apply "readlist" []),VarDec "list2" Nothing (Sequence (Assign (Ident "buffer") (Apply "getchar" [])) (Apply "readlist" []))] (Apply "printlist" [Apply "merge" [LValue (Ident "list1"),LValue (Ident "list2")]]))

p7 = Program (Let [VarDec "N" Nothing (IntLit 8),TypeDecs [TypeDec "intArray" (Array "int")],VarDec "row" Nothing (ArrayVal "intArray" (LValue (Ident "N")) (IntLit 0)),VarDec "col" Nothing (ArrayVal "intArray" (LValue (Ident "N")) (IntLit 0)),VarDec "diag1" Nothing (ArrayVal "intArray" (Op "-" (Op "+" (LValue (Ident "N")) (LValue (Ident "N"))) (IntLit 1)) (IntLit 0)),VarDec "diag2" Nothing (ArrayVal "intArray" (Op "-" (Op "+" (LValue (Ident "N")) (LValue (Ident "N"))) (IntLit 1)) (IntLit 0)),FunDecs [FunDec "printboard" [] Nothing (Sequence (For "i" (IntLit 0) (Op "-" (LValue (Ident "N")) (IntLit 1)) (Sequence (For "j" (IntLit 0) (Op "-" (LValue (Ident "N")) (IntLit 1)) (Apply "print" [If (Op "=" (LValue (Ident "j")) (LValue (Sub (Ident "col") (LValue (Ident "i"))))) (StringLit "\" O\"") (StringLit "\" .\"")])) (Apply "print" [StringLit "\"\\n\""]))) (Apply "print" [StringLit "\"\\n\""])),FunDec "try" [TypedVar "c" "int"] Nothing (If (Op "=" (LValue (Ident "N")) (LValue (Ident "c"))) (Apply "printboard" []) (For "r" (IntLit 0) (Op "-" (LValue (Ident "N")) (IntLit 1)) (If (Op "&" (Op "&" (Op "=" (IntLit 0) (LValue (Sub (Ident "row") (LValue (Ident "r"))))) (Op "=" (IntLit 0) (LValue (Sub (Ident "diag1") (Op "+" (LValue (Ident "r")) (LValue (Ident "c"))))))) (Op "=" (IntLit 0) (LValue (Sub (Ident "diag2") (Op "-" (Op "+" (LValue (Ident "r")) (IntLit 7)) (LValue (Ident "c"))))))) (Sequence (Assign (Sub (Ident "row") (LValue (Ident "r"))) (IntLit 1)) (Sequence (Assign (Sub (Ident "diag1") (Op "+" (LValue (Ident "r")) (LValue (Ident "c")))) (IntLit 1)) (Sequence (Assign (Sub (Ident "diag2") (Op "-" (Op "+" (LValue (Ident "r")) (IntLit 7)) (LValue (Ident "c")))) (IntLit 1)) (Sequence (Assign (Sub (Ident "col") (LValue (Ident "c"))) (LValue (Ident "r"))) (Sequence (Apply "try" [Op "+" (LValue (Ident "c")) (IntLit 1)]) (Sequence (Assign (Sub (Ident "row") (LValue (Ident "r"))) (IntLit 0)) (Sequence (Assign (Sub (Ident "diag1") (Op "+" (LValue (Ident "r")) (LValue (Ident "c")))) (IntLit 0)) (Assign (Sub (Ident "diag2") (Op "-" (Op "+" (LValue (Ident "r")) (IntLit 7)) (LValue (Ident "c")))) (IntLit 0))))))))) Skip)))]] (Apply "try" [IntLit 0]))
