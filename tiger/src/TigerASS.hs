{-# LANGUAGE DeriveGeneric #-}

-- TigerASS means TigerAS Simple, as it skips the Pos info

module TigerASS where

import Data.Data
import GHC.Generics
import TigerTypes hiding (VarIdent, TypedVar, TypeIdent, Ident, Type, Id)
import Data.String
-- Args --------------------------------------------------------
type Args = [Expr]
-- AssignField -------------------------------------------------
data AssignField = AssignField (VarIdent) (Expr)
                 deriving (Generic, Show, Data)
-- AssignFields ------------------------------------------------
type AssignFields = [AssignField]
-- DeclGroup ---------------------------------------------------
data DeclGroup = VarDec (VarIdent) ((Maybe TypeIdent)) (Expr)
               | TypeDecs (TypeDecs)
               | FunDecs (FunDecs)
               deriving (Generic, Show, Data)
-- Declarations ------------------------------------------------
type Declarations = [DeclGroup]
-- Expr --------------------------------------------------------
data Expr = LValue (LValue)
          | Apply (VarIdent) (Args)
          | RecordVal (TypeIdent) (AssignFields)
          | ArrayVal (TypeIdent) (Expr) (Expr)
          | IntLit (Integer)
          | StringLit (String)
          | While (Expr) (Expr)
          | For (VarIdent) (Expr) (Expr) (Expr)
          | If (Expr) (Expr) (Expr)
          | Let (Declarations) (Expr)
          | Assign (LValue) (Expr)
          | Op (String) (Expr) (Expr)
          | UnOp (String) (Expr)
          | Skip
          | Nil
          | Break
          | Sequence (Expr) (Expr)
          deriving (Generic, Show, Data)
-- FunDec ------------------------------------------------------
data FunDec = FunDec (VarIdent) (([TypedVar])) ((Maybe TypeIdent)) (Expr)
            deriving (Generic, Show, Data)
-- FunDecs -----------------------------------------------------
type FunDecs = [FunDec]
-- LValue ------------------------------------------------------
data LValue = Sub (LValue) (Expr)
            | Dot (LValue) (VarIdent)
            | Ident (VarIdent)
            deriving (Generic, Show, Data)
-- Program -----------------------------------------------------
data Program = Program (Expr)
             deriving (Generic, Show, Data)
-- TypeDec -----------------------------------------------------
data TypeDec = TypeDec (TypeIdent) (Type)
             deriving (Generic, Show, Data)
-- TypeDecs ----------------------------------------------------
type TypeDecs = [TypeDec]
---

data Ident = Id String
    deriving (Eq, Ord, Data)

instance Show Ident where
    show (Id x) = show x

instance IsString Ident where
    fromString = Id

type VarIdent = Ident

type TypeIdent = Ident

data Type
   = Var    TypeIdent
   | Array  TypeIdent
   | Record [TypedVar]  deriving (Show, Data)

data TypedVar = TypedVar VarIdent TypeIdent  deriving (Show, Data)

