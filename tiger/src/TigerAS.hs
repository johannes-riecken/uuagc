{-# LANGUAGE DeriveGeneric #-}


-- UUAGC 0.9.57 (TigerAS.ag)
module TigerAS where


import GHC.Generics
import TigerTypes
import UU.Scanner.Position
import qualified TigerASS as A

-- Args --------------------------------------------------------
type Args = [Expr]

-- AssignField -------------------------------------------------
data AssignField = AssignField (VarIdent) (Expr)
                 deriving (Generic)
assignFieldToAss (AssignField a b) = A.AssignField (identToAss a) (exprToAss b)

-- AssignFields ------------------------------------------------
type AssignFields = [AssignField]

-- DeclGroup ---------------------------------------------------
data DeclGroup = VarDec (Pos) (VarIdent) ((Maybe TypeIdent)) (Expr)
               | TypeDecs (TypeDecs)
               | FunDecs (FunDecs)
               deriving (Generic)
declGroupToAss :: DeclGroup -> A.DeclGroup
declGroupToAss (VarDec _ a b c) = A.VarDec (identToAss a) (fmap identToAss b) (exprToAss c)
declGroupToAss (TypeDecs xs) = A.TypeDecs (map typeDecToAss xs)
declGroupToAss (FunDecs xs) = A.FunDecs (map funDecToAss xs)

identToAss (Id x _) = A.Id x

-- Declarations ------------------------------------------------
type Declarations = [DeclGroup]

-- Expr --------------------------------------------------------
data Expr = LValue (LValue)
          | Apply (VarIdent) (Args)
          | RecordVal (TypeIdent) (AssignFields)
          | ArrayVal (TypeIdent) (Expr) (Expr)
          | IntLit (Integer) (Pos)
          | StringLit (String) (Pos)
          | While (Pos) (Expr) (Expr)
          | For (Pos) (VarIdent) (Expr) (Expr) (Expr)
          | If (Pos) (Expr) (Expr) (Expr)
          | Let (Pos) (Declarations) (Expr)
          | Assign (LValue) (Pos) (Expr)
          | Op (String) (Pos) (Expr) (Expr)
          | UnOp (Pos) (String) (Expr)
          | Skip
          | Nil (Pos)
          | Break (Pos)
          | Sequence (Expr) (Expr)
          deriving (Generic)

exprToAss (LValue a) = A.LValue (lValueToAss a)
exprToAss (Apply a b) = A.Apply (identToAss a) (map exprToAss b)
exprToAss (RecordVal a b) = A.RecordVal (identToAss a) (map assignFieldToAss b)
exprToAss (ArrayVal a b c) = A.ArrayVal (identToAss a) (exprToAss b) (exprToAss c)
exprToAss (IntLit a _) = A.IntLit a
exprToAss (StringLit a _) = A.StringLit a
exprToAss (While _ a b) = A.While (exprToAss a) (exprToAss b)
exprToAss (For _ a b c d) = A.For (identToAss a) (exprToAss b) (exprToAss c) (exprToAss d)
exprToAss (If _ a b c) = A.If (exprToAss a) (exprToAss b) (exprToAss c)
exprToAss (Let _ a b) = A.Let (map declGroupToAss a) (exprToAss b)
exprToAss (Assign a _ b) = A.Assign (lValueToAss a) (exprToAss b)
exprToAss (Op a _ b c) = A.Op a (exprToAss b) (exprToAss c)
exprToAss (UnOp _ a b) = A.UnOp a (exprToAss b)
exprToAss Skip = A.Skip
exprToAss (Nil _) = A.Nil
exprToAss (Break _) = A.Break
exprToAss (Sequence a b) = A.Sequence (exprToAss a) (exprToAss b)

-- FunDec ------------------------------------------------------
data FunDec = FunDec (Pos) (VarIdent) (([TypedVar])) ((Maybe TypeIdent)) (Expr)
            deriving (Generic)
funDecToAss (FunDec _ a b c d) = A.FunDec (identToAss a) (map typedVarToAss b) (fmap identToAss c) (exprToAss d)

-- FunDecs -----------------------------------------------------
type FunDecs = [FunDec]

-- LValue ------------------------------------------------------
data LValue = Sub (Pos) (LValue) (Expr)
            | Dot (Pos) (LValue) (VarIdent)
            | Ident (VarIdent)
            deriving (Generic)
lValueToAss (Sub _ a b) = A.Sub (lValueToAss a) (exprToAss b)
lValueToAss (Dot _ a b) = A.Dot (lValueToAss a) (identToAss b)
lValueToAss (Ident a) = A.Ident (identToAss a)

-- Program -----------------------------------------------------
data Program = Program (Expr)
             deriving (Generic)
programToAss (Program a) = A.Program (exprToAss a)

-- TypeDec -----------------------------------------------------
data TypeDec = TypeDec (Pos) (TypeIdent) (Type)
             deriving (Generic)
typeDecToAss (TypeDec _ x y) = A.TypeDec (identToAss x) (typeToAss y)

-- TypeDecs ----------------------------------------------------
type TypeDecs = [TypeDec]

---

typeToAss (Var a) = A.Var (identToAss a)
typeToAss (Array a) = A.Array (identToAss a)
typeToAss (Record xs) = A.Record (map typedVarToAss xs)

typedVarToAss (TypedVar a b) = A.TypedVar (identToAss a) (identToAss b)
