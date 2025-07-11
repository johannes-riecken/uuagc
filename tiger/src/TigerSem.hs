

-- UUAGC 0.9.57 (TigerSem.ag)
module TigerSem where


import TigerTypes
import UU.Scanner.Position


import TigerAS
import Control.Monad(mplus)
import Data.List(sort)
import Data.Maybe(fromMaybe)
import qualified Data.Sequence as Seq
import Data.Sequence(Seq, (><), singleton,empty)
import Data.Foldable(toList)
import Data.Map(Map,unionWith,keys,insert,elems,mapWithKey)
import qualified Data.Map as Map(lookup,empty,fromList,insert)
import TigerError

type Errors = Seq Error

union a b = unionWith const a b
type TypeEnv   = Map TypeIdent (Pos, TYPE)
type VarEnv    = Map VarIdent  (Pos,VarType)
type TypeSyns  = Map TypeIdent (Pos,TypeIdent)
--type RecordEnv = Map TypeRef (Map VarIdent TypeRef)
--type ArrayEnv  = Map TypeRef TypeRef

data VarType = VarType TYPE
             | FunType [TYPE]      -- argument types
                        TYPE       -- return type

{-
loopCounterType,errorType, emptyRecType, voidType, intType, strType :: TYPE
loopCounterType = (-6)
errorType = (-5)
emptyRecType   = (-4)
voidType  = (-3)
intType   = (-2)
strType   = (-1)
-}
{-
unaryOps  = fromList [("-", (intType,intType))]
binaryOps = fromList [ (o,iii) | o <- ["*", "/", "+", "-"  ,">=", "<=", "=", "<>", "<", ">","&","|" ]]
  where iii = (intType,intType,intType)
-}

initTypeEnv     = Map.fromList (map toIdent
                  [ ("int", INT)
                  , ("string", STRING)
		  ])

toIdent (n,t) = (Id n noPos,(noPos, t))

initVarEnv = Map.fromList (map toIdent
             [ ("print"    , procedure [STRING])
	     , ("flush"    , procedure []      )
	     , ("exit"     , procedure [INT]   )
	     , ("getchar"  , function []                 STRING )
	     , ("ord"      , function [STRING]           INT    )
	     , ("chr"      , function [INT]              STRING )
	     , ("size"     , function [STRING]           INT    )
	     , ("substring", function [STRING, INT, INT] STRING )
	     , ("concat"   , function [STRING, STRING]   STRING )
	     , ("not"      , function [INT]              INT    )
	     ])

procedure args    = FunType args VOID
function args res = FunType args res

findType env n = case lookupIdent n env of
                   Just x  -> (empty, x)
                   Nothing -> (singleton (UndeclaredType n), ERROR)

findVar env n = case lookupIdent n env of
                   Just x -> case x of
                                  VarType t   -> (empty, t)
                                  FunType _ _ -> (singleton (NotVarType n), ERROR)
                   Nothing    -> (singleton (UndeclaredVar n), ERROR)
findFunction env n = case lookupIdent n env of
                   Just x -> case x of
                                  VarType t   -> (singleton (NotFunType n), [], ERROR)
                                  FunType a r -> (empty, a,r)
                   Nothing    -> (singleton (UndeclaredFun n), [], ERROR)


lookupIdent :: Ident -> Map Ident (Pos,a) -> Maybe a
lookupIdent i env = fmap snd (Map.lookup i env)

compilerError msg = error ("compiler error: " ++ msg)


recordFields :: TypeEnv -> [TypedVar] -> (Errors,Map Ident (Pos,TYPE))
recordFields tenv tvs = foldr field (empty,Map.empty) tvs
  where field (TypedVar v t) ~(es,fs)
                = case lookupPos v fs of
                        Just p  -> (es >< singleton (DupRecordFieldDecl v p),fs)
                        Nothing -> let (err,t')   = findType tenv t
                                   in (es >< err,insertIdent v t' fs)



lookupPos :: Ident -> Map Ident (Pos,a) -> Maybe Pos
lookupPos i env = fmap fst (Map.lookup i env)

insertIdent :: Ident -> a -> Map Ident (Pos,a) -> Map Ident (Pos,a)
insertIdent i@(Id n p) val = insert i (p,val)

addTypeDecls :: (TypeEnv,TypeSyns) -> TypeEnv -> (Errors,TypeEnv)
addTypeDecls (new,syns) env = (errors, fmap (snd.snd) resolve `union`  rest)
 where  rest     = new `union` env
        errors   = foldr (><) empty (map (fst.snd) (elems resolve))
        resolve :: Map Ident ([Ident],(Seq Error,(Pos,TYPE)))
        resolve  = mapWithKey find syns
           where find l (p,v)
                   = case Map.lookup v resolve of
                            Just ~(vs,~(_,b)) -> (v:vs,  if v `elem` vs
                                                            then (singleton (CyclicType l)
                                                                 ,(p,ERROR)
                                                                 )
                                                            else (empty,(p, snd b))
                                                 )
                            Nothing           -> let (es,tp) = findType rest v
                                                 in ([], (es, (p,tp)))


arrayComponentType :: Pos -> TYPE -> (Errors,TYPE)
arrayComponentType _ ERROR          = (empty,ERROR)
arrayComponentType _ (ARRAY _ _ c)  = (empty,c)
arrayComponentType p tp             = (singleton (NotArrayType p),ERROR)

recordFieldType :: Pos -> Map VarIdent (Pos,TYPE) -> Ident -> (Errors,TYPE)
recordFieldType p fields ident = case lookupIdent ident fields of
                                        Nothing -> (singleton (NoSuchField p ident), ERROR)
                                        Just t  -> (empty,t)

recordType :: Pos -> TYPE -> (Errors,Map Ident (Pos,TYPE))
recordType _ ERROR           = (empty,Map.empty)
recordType p (RECORD n _ fs) = (empty,fs)
recordType p NIL             = (singleton (UnknownType p),Map.empty)
recordType p tp              = (singleton (NotRecordType p),Map.empty)

match a b = maybe False (const True) (meet a b)

meet a     ERROR          = Just a
meet ERROR b              = Just b
meet LOOPCOUNTER INT      = Just LOOPCOUNTER
meet INT LOOPCOUNTER      = Just LOOPCOUNTER
meet a@(RECORD _ _ _) NIL = Just a
meet NIL b@(RECORD _ _ _) = Just b
meet a b | a == b         = Just a
         | otherwise      = Nothing


meetErr a b = case meet a b of
            Nothing -> (singleton (TypeMisMatch a b), ERROR)
            Just t  -> (empty, t)
--Nil?
-- Args --------------------------------------------------------
-- cata
sem_Args :: Args ->
            T_Args
sem_Args list =
    (Prelude.foldr sem_Args_Cons sem_Args_Nil (Prelude.map sem_Expr list))
-- semantic domain
type T_Args = Errors ->
              ([TYPE]) ->
              TypeEnv ->
              Int ->
              VarEnv ->
              ( Errors,Int,Int)
sem_Args_Cons :: T_Expr ->
                 T_Args ->
                 T_Args
sem_Args_Cons hd_ tl_ =
    (\ _lhsIerrors
       _lhsIexpects
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _hdOexpect :: TYPE
              _tlOexpects :: ([TYPE])
              _lhsOsize :: Int
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _hdOerrors :: Errors
              _hdOtypeEnv :: TypeEnv
              _hdOtypecounter :: Int
              _hdOvarEnv :: VarEnv
              _tlOerrors :: Errors
              _tlOtypeEnv :: TypeEnv
              _tlOtypecounter :: Int
              _tlOvarEnv :: VarEnv
              _hdIerrors :: Errors
              _hdItp :: TYPE
              _hdItypecounter :: Int
              _tlIerrors :: Errors
              _tlIsize :: Int
              _tlItypecounter :: Int
              _hdOexpect =
                  head _lhsIexpects
              _tlOexpects =
                  tail _lhsIexpects
              _lhsOsize =
                  1 + _tlIsize
              _lhsOerrors =
                  _tlIerrors
              _lhsOtypecounter =
                  _tlItypecounter
              _hdOerrors =
                  _lhsIerrors
              _hdOtypeEnv =
                  _lhsItypeEnv
              _hdOtypecounter =
                  _lhsItypecounter
              _hdOvarEnv =
                  _lhsIvarEnv
              _tlOerrors =
                  _hdIerrors
              _tlOtypeEnv =
                  _lhsItypeEnv
              _tlOtypecounter =
                  _hdItypecounter
              _tlOvarEnv =
                  _lhsIvarEnv
              ( _hdIerrors,_hdItp,_hdItypecounter) =
                  hd_ _hdOerrors _hdOexpect _hdOtypeEnv _hdOtypecounter _hdOvarEnv
              ( _tlIerrors,_tlIsize,_tlItypecounter) =
                  tl_ _tlOerrors _tlOexpects _tlOtypeEnv _tlOtypecounter _tlOvarEnv
          in  ( _lhsOerrors,_lhsOsize,_lhsOtypecounter)))
sem_Args_Nil :: T_Args
sem_Args_Nil =
    (\ _lhsIerrors
       _lhsIexpects
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOsize :: Int
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _lhsOsize =
                  0
              _lhsOerrors =
                  _lhsIerrors
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOsize,_lhsOtypecounter)))
-- AssignField -------------------------------------------------
-- cata
sem_AssignField :: AssignField ->
                   T_AssignField
sem_AssignField (AssignField _ident _expr) =
    (sem_AssignField_AssignField _ident (sem_Expr _expr))
-- semantic domain
type T_AssignField = Errors ->
                     TYPE ->
                     TypeEnv ->
                     Int ->
                     VarEnv ->
                     ( Errors,VarIdent,Int)
sem_AssignField_AssignField :: VarIdent ->
                               T_Expr ->
                               T_AssignField
sem_AssignField_AssignField ident_ expr_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOname :: VarIdent
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _exprOerrors :: Errors
              _exprOexpect :: TYPE
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              _lhsOname =
                  ident_
              _lhsOerrors =
                  _exprIerrors
              _lhsOtypecounter =
                  _exprItypecounter
              _exprOerrors =
                  _lhsIerrors
              _exprOexpect =
                  _lhsIexpect
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lhsItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
          in  ( _lhsOerrors,_lhsOname,_lhsOtypecounter)))
-- AssignFields ------------------------------------------------
-- cata
sem_AssignFields :: AssignFields ->
                    T_AssignFields
sem_AssignFields list =
    (Prelude.foldr sem_AssignFields_Cons sem_AssignFields_Nil (Prelude.map sem_AssignField list))
-- semantic domain
type T_AssignFields = Errors ->
                      ([TYPE]) ->
                      TypeEnv ->
                      Int ->
                      VarEnv ->
                      ( Errors,([VarIdent]),Int)
sem_AssignFields_Cons :: T_AssignField ->
                         T_AssignFields ->
                         T_AssignFields
sem_AssignFields_Cons hd_ tl_ =
    (\ _lhsIerrors
       _lhsIexpects
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOnames :: ([VarIdent])
              _hdOexpect :: TYPE
              _tlOexpects :: ([TYPE])
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _hdOerrors :: Errors
              _hdOtypeEnv :: TypeEnv
              _hdOtypecounter :: Int
              _hdOvarEnv :: VarEnv
              _tlOerrors :: Errors
              _tlOtypeEnv :: TypeEnv
              _tlOtypecounter :: Int
              _tlOvarEnv :: VarEnv
              _hdIerrors :: Errors
              _hdIname :: VarIdent
              _hdItypecounter :: Int
              _tlIerrors :: Errors
              _tlInames :: ([VarIdent])
              _tlItypecounter :: Int
              _lhsOnames =
                  _hdIname : _tlInames
              _hdOexpect =
                  head _lhsIexpects
              _tlOexpects =
                  tail _lhsIexpects
              _lhsOerrors =
                  _tlIerrors
              _lhsOtypecounter =
                  _tlItypecounter
              _hdOerrors =
                  _lhsIerrors
              _hdOtypeEnv =
                  _lhsItypeEnv
              _hdOtypecounter =
                  _lhsItypecounter
              _hdOvarEnv =
                  _lhsIvarEnv
              _tlOerrors =
                  _hdIerrors
              _tlOtypeEnv =
                  _lhsItypeEnv
              _tlOtypecounter =
                  _hdItypecounter
              _tlOvarEnv =
                  _lhsIvarEnv
              ( _hdIerrors,_hdIname,_hdItypecounter) =
                  hd_ _hdOerrors _hdOexpect _hdOtypeEnv _hdOtypecounter _hdOvarEnv
              ( _tlIerrors,_tlInames,_tlItypecounter) =
                  tl_ _tlOerrors _tlOexpects _tlOtypeEnv _tlOtypecounter _tlOvarEnv
          in  ( _lhsOerrors,_lhsOnames,_lhsOtypecounter)))
sem_AssignFields_Nil :: T_AssignFields
sem_AssignFields_Nil =
    (\ _lhsIerrors
       _lhsIexpects
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOnames :: ([VarIdent])
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _lhsOnames =
                  []
              _lhsOerrors =
                  _lhsIerrors
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOnames,_lhsOtypecounter)))
-- DeclGroup ---------------------------------------------------
-- cata
sem_DeclGroup :: DeclGroup ->
                 T_DeclGroup
sem_DeclGroup (VarDec _pos _ident _tp _expr) =
    (sem_DeclGroup_VarDec _pos _ident _tp (sem_Expr _expr))
sem_DeclGroup (TypeDecs _decs) =
    (sem_DeclGroup_TypeDecs (sem_TypeDecs _decs))
sem_DeclGroup (FunDecs _decs) =
    (sem_DeclGroup_FunDecs (sem_FunDecs _decs))
-- semantic domain
type T_DeclGroup = Errors ->
                   TypeEnv ->
                   Int ->
                   VarEnv ->
                   ( Errors,TypeEnv,Int,VarEnv)
sem_DeclGroup_VarDec :: Pos ->
                        VarIdent ->
                        (Maybe TypeIdent) ->
                        T_Expr ->
                        T_DeclGroup
sem_DeclGroup_VarDec pos_ ident_ tp_ expr_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOvarEnv :: VarEnv
              _exprOexpect :: TYPE
              _exprOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtypeEnv :: TypeEnv
              _lhsOtypecounter :: Int
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              _lhsOvarEnv =
                  insertIdent ident_ (VarType _theType) _lhsIvarEnv
              (_errs,_theType) =
                  case tp_ of
                       Just t -> findType _lhsItypeEnv t
                       Nothing -> case _exprItp of
                                   NIL  -> (singleton (UnknownType (getPos ident_)),ERROR)
                                   VOID -> (singleton (InitWithVoid (getPos ident_)),ERROR)
                                   _    -> (empty,_exprItp)
              _exprOexpect =
                  _theType
              _exprOerrors =
                  _lhsIerrors >< _errs
              _lhsOerrors =
                  _exprIerrors
              _lhsOtypeEnv =
                  _lhsItypeEnv
              _lhsOtypecounter =
                  _exprItypecounter
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lhsItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
          in  ( _lhsOerrors,_lhsOtypeEnv,_lhsOtypecounter,_lhsOvarEnv)))
sem_DeclGroup_TypeDecs :: T_TypeDecs ->
                          T_DeclGroup
sem_DeclGroup_TypeDecs decs_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _decsOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtypeEnv :: TypeEnv
              _lhsOtypecounter :: Int
              _lhsOvarEnv :: VarEnv
              _decsOtypeEnv :: TypeEnv
              _decsOtypecounter :: Int
              _decsIerrors :: Errors
              _decsItypecounter :: Int
              _decsItypedecs :: ((TypeEnv, TypeSyns))
              (_errs,_typeEnv) =
                  addTypeDecls _decsItypedecs _lhsItypeEnv
              _decsOerrors =
                  _lhsIerrors >< _errs
              _lhsOerrors =
                  _decsIerrors
              _lhsOtypeEnv =
                  _typeEnv
              _lhsOtypecounter =
                  _decsItypecounter
              _lhsOvarEnv =
                  _lhsIvarEnv
              _decsOtypeEnv =
                  _typeEnv
              _decsOtypecounter =
                  _lhsItypecounter
              ( _decsIerrors,_decsItypecounter,_decsItypedecs) =
                  decs_ _decsOerrors _decsOtypeEnv _decsOtypecounter
          in  ( _lhsOerrors,_lhsOtypeEnv,_lhsOtypecounter,_lhsOvarEnv)))
sem_DeclGroup_FunDecs :: T_FunDecs ->
                         T_DeclGroup
sem_DeclGroup_FunDecs decs_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtypeEnv :: TypeEnv
              _lhsOtypecounter :: Int
              _lhsOvarEnv :: VarEnv
              _decsOerrors :: Errors
              _decsOtypeEnv :: TypeEnv
              _decsOtypecounter :: Int
              _decsOvarEnv :: VarEnv
              _decsIerrors :: Errors
              _decsIfundecs :: VarEnv
              _decsItypecounter :: Int
              _varEnv =
                  _decsIfundecs `union` _lhsIvarEnv
              _lhsOerrors =
                  _decsIerrors
              _lhsOtypeEnv =
                  _lhsItypeEnv
              _lhsOtypecounter =
                  _decsItypecounter
              _lhsOvarEnv =
                  _varEnv
              _decsOerrors =
                  _lhsIerrors
              _decsOtypeEnv =
                  _lhsItypeEnv
              _decsOtypecounter =
                  _lhsItypecounter
              _decsOvarEnv =
                  _varEnv
              ( _decsIerrors,_decsIfundecs,_decsItypecounter) =
                  decs_ _decsOerrors _decsOtypeEnv _decsOtypecounter _decsOvarEnv
          in  ( _lhsOerrors,_lhsOtypeEnv,_lhsOtypecounter,_lhsOvarEnv)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_DeclGroup list))
-- semantic domain
type T_Declarations = Errors ->
                      TypeEnv ->
                      Int ->
                      VarEnv ->
                      ( Errors,TypeEnv,Int,VarEnv)
sem_Declarations_Cons :: T_DeclGroup ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtypeEnv :: TypeEnv
              _lhsOtypecounter :: Int
              _lhsOvarEnv :: VarEnv
              _hdOerrors :: Errors
              _hdOtypeEnv :: TypeEnv
              _hdOtypecounter :: Int
              _hdOvarEnv :: VarEnv
              _tlOerrors :: Errors
              _tlOtypeEnv :: TypeEnv
              _tlOtypecounter :: Int
              _tlOvarEnv :: VarEnv
              _hdIerrors :: Errors
              _hdItypeEnv :: TypeEnv
              _hdItypecounter :: Int
              _hdIvarEnv :: VarEnv
              _tlIerrors :: Errors
              _tlItypeEnv :: TypeEnv
              _tlItypecounter :: Int
              _tlIvarEnv :: VarEnv
              _lhsOerrors =
                  _tlIerrors
              _lhsOtypeEnv =
                  _tlItypeEnv
              _lhsOtypecounter =
                  _tlItypecounter
              _lhsOvarEnv =
                  _tlIvarEnv
              _hdOerrors =
                  _lhsIerrors
              _hdOtypeEnv =
                  _lhsItypeEnv
              _hdOtypecounter =
                  _lhsItypecounter
              _hdOvarEnv =
                  _lhsIvarEnv
              _tlOerrors =
                  _hdIerrors
              _tlOtypeEnv =
                  _hdItypeEnv
              _tlOtypecounter =
                  _hdItypecounter
              _tlOvarEnv =
                  _hdIvarEnv
              ( _hdIerrors,_hdItypeEnv,_hdItypecounter,_hdIvarEnv) =
                  hd_ _hdOerrors _hdOtypeEnv _hdOtypecounter _hdOvarEnv
              ( _tlIerrors,_tlItypeEnv,_tlItypecounter,_tlIvarEnv) =
                  tl_ _tlOerrors _tlOtypeEnv _tlOtypecounter _tlOvarEnv
          in  ( _lhsOerrors,_lhsOtypeEnv,_lhsOtypecounter,_lhsOvarEnv)))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtypeEnv :: TypeEnv
              _lhsOtypecounter :: Int
              _lhsOvarEnv :: VarEnv
              _lhsOerrors =
                  _lhsIerrors
              _lhsOtypeEnv =
                  _lhsItypeEnv
              _lhsOtypecounter =
                  _lhsItypecounter
              _lhsOvarEnv =
                  _lhsIvarEnv
          in  ( _lhsOerrors,_lhsOtypeEnv,_lhsOtypecounter,_lhsOvarEnv)))
-- Expr --------------------------------------------------------
-- cata
sem_Expr :: Expr ->
            T_Expr
sem_Expr (LValue _lvalue) =
    (sem_Expr_LValue (sem_LValue _lvalue))
sem_Expr (Apply _ident _args) =
    (sem_Expr_Apply _ident (sem_Args _args))
sem_Expr (RecordVal _ident _fields) =
    (sem_Expr_RecordVal _ident (sem_AssignFields _fields))
sem_Expr (ArrayVal _ident _size _init) =
    (sem_Expr_ArrayVal _ident (sem_Expr _size) (sem_Expr _init))
sem_Expr (IntLit _value _pos) =
    (sem_Expr_IntLit _value _pos)
sem_Expr (StringLit _value _pos) =
    (sem_Expr_StringLit _value _pos)
sem_Expr (While _pos _cond _body) =
    (sem_Expr_While _pos (sem_Expr _cond) (sem_Expr _body))
sem_Expr (For _pos _ident _low _hi _body) =
    (sem_Expr_For _pos _ident (sem_Expr _low) (sem_Expr _hi) (sem_Expr _body))
sem_Expr (If _pos _cond _thenPart _elsePart) =
    (sem_Expr_If _pos (sem_Expr _cond) (sem_Expr _thenPart) (sem_Expr _elsePart))
sem_Expr (Let _pos _decls _body) =
    (sem_Expr_Let _pos (sem_Declarations _decls) (sem_Expr _body))
sem_Expr (Assign _lvalue _pos _expr) =
    (sem_Expr_Assign (sem_LValue _lvalue) _pos (sem_Expr _expr))
sem_Expr (Op _op _pos _left _right) =
    (sem_Expr_Op _op _pos (sem_Expr _left) (sem_Expr _right))
sem_Expr (UnOp _pos _op _expr) =
    (sem_Expr_UnOp _pos _op (sem_Expr _expr))
sem_Expr (Skip) =
    (sem_Expr_Skip)
sem_Expr (Nil _pos) =
    (sem_Expr_Nil _pos)
sem_Expr (Break _pos) =
    (sem_Expr_Break _pos)
sem_Expr (Sequence _left _right) =
    (sem_Expr_Sequence (sem_Expr _left) (sem_Expr _right))
-- semantic domain
type T_Expr = Errors ->
              TYPE ->
              TypeEnv ->
              Int ->
              VarEnv ->
              ( Errors,TYPE,Int)
sem_Expr_LValue :: T_LValue ->
                   T_Expr
sem_Expr_LValue lvalue_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lvalueOexpect :: TYPE
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _lvalueOerrors :: Errors
              _lvalueOtypeEnv :: TypeEnv
              _lvalueOtypecounter :: Int
              _lvalueOvarEnv :: VarEnv
              _lvalueIerrors :: Errors
              _lvalueItp :: TYPE
              _lvalueItypecounter :: Int
              _tp =
                  if _lvalueItp == LOOPCOUNTER
                      then INT
                      else _lvalueItp
              _lvalueOexpect =
                  _lhsIexpect
              _lhsOerrors =
                  _lvalueIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lvalueItypecounter
              _lvalueOerrors =
                  _lhsIerrors
              _lvalueOtypeEnv =
                  _lhsItypeEnv
              _lvalueOtypecounter =
                  _lhsItypecounter
              _lvalueOvarEnv =
                  _lhsIvarEnv
              ( _lvalueIerrors,_lvalueItp,_lvalueItypecounter) =
                  lvalue_ _lvalueOerrors _lvalueOexpect _lvalueOtypeEnv _lvalueOtypecounter _lvalueOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Apply :: VarIdent ->
                  T_Args ->
                  T_Expr
sem_Expr_Apply ident_ args_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOtp :: TYPE
              _argsOexpects :: ([TYPE])
              _argsOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _argsOtypeEnv :: TypeEnv
              _argsOtypecounter :: Int
              _argsOvarEnv :: VarEnv
              _argsIerrors :: Errors
              _argsIsize :: Int
              _argsItypecounter :: Int
              (_errs,_argTps,_retTp) =
                  findFunction _lhsIvarEnv ident_
              _lhsOtp =
                  _retTp
              _argsOexpects =
                  _argTps ++ repeat ERROR
              _argsOerrors =
                  _lhsIerrors ><
                  _errs ><
                  (case compare _argsIsize (length _argTps) of
                     LT -> singleton (TooFewArguments  ident_)
                     GT -> singleton (TooManyArguments ident_)
                     EQ -> empty) ><
                  if match _lhsIexpect _retTp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _retTp)
              _lhsOerrors =
                  _argsIerrors
              _lhsOtypecounter =
                  _argsItypecounter
              _argsOtypeEnv =
                  _lhsItypeEnv
              _argsOtypecounter =
                  _lhsItypecounter
              _argsOvarEnv =
                  _lhsIvarEnv
              ( _argsIerrors,_argsIsize,_argsItypecounter) =
                  args_ _argsOerrors _argsOexpects _argsOtypeEnv _argsOtypecounter _argsOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_RecordVal :: TypeIdent ->
                      T_AssignFields ->
                      T_Expr
sem_Expr_RecordVal ident_ fields_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _fieldsOexpects :: ([TYPE])
              _fieldsOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _fieldsOtypeEnv :: TypeEnv
              _fieldsOtypecounter :: Int
              _fieldsOvarEnv :: VarEnv
              _fieldsIerrors :: Errors
              _fieldsInames :: ([VarIdent])
              _fieldsItypecounter :: Int
              (_err1,_tp) =
                  findType _lhsItypeEnv ident_
              (_err2,_fieldEnv) =
                  recordType (getPos ident_) _tp
              (_err3,_expFields) =
                  let f i ~(err,ts) = case recordFieldType (getPos i) _fieldEnv i of
                                        (e,t) -> (err><e,t:ts)
                  in foldr f (empty,[]) _fieldsInames
              _notInit =
                  foldr (Seq.<|) empty [ FieldNotInit f | f <- keys _fieldEnv, not (f `elem` _fieldsInames)]
              _fieldsOexpects =
                  _expFields
              _fieldsOerrors =
                  _lhsIerrors ><
                  _err1 ><
                  _err2 ><
                  _err3 ><
                  _notInit ><
                  if match _lhsIexpect _tp
                    then empty
                    else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _fieldsIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _fieldsItypecounter
              _fieldsOtypeEnv =
                  _lhsItypeEnv
              _fieldsOtypecounter =
                  _lhsItypecounter
              _fieldsOvarEnv =
                  _lhsIvarEnv
              ( _fieldsIerrors,_fieldsInames,_fieldsItypecounter) =
                  fields_ _fieldsOerrors _fieldsOexpects _fieldsOtypeEnv _fieldsOtypecounter _fieldsOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_ArrayVal :: TypeIdent ->
                     T_Expr ->
                     T_Expr ->
                     T_Expr
sem_Expr_ArrayVal ident_ size_ init_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _sizeOexpect :: TYPE
              _initOexpect :: TYPE
              _initOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _sizeOerrors :: Errors
              _sizeOtypeEnv :: TypeEnv
              _sizeOtypecounter :: Int
              _sizeOvarEnv :: VarEnv
              _initOtypeEnv :: TypeEnv
              _initOtypecounter :: Int
              _initOvarEnv :: VarEnv
              _sizeIerrors :: Errors
              _sizeItp :: TYPE
              _sizeItypecounter :: Int
              _initIerrors :: Errors
              _initItp :: TYPE
              _initItypecounter :: Int
              (_err1,_tp) =
                  findType _lhsItypeEnv ident_
              (_err2,_compTp) =
                  arrayComponentType (getPos ident_) _tp
              _sizeOexpect =
                  INT
              _initOexpect =
                  _compTp
              _initOerrors =
                  _lhsIerrors ><
                  _err1 ><
                  _err2 ><
                  if match _lhsIexpect _tp
                    then empty
                    else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _initIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _initItypecounter
              _sizeOerrors =
                  _lhsIerrors
              _sizeOtypeEnv =
                  _lhsItypeEnv
              _sizeOtypecounter =
                  _lhsItypecounter
              _sizeOvarEnv =
                  _lhsIvarEnv
              _initOtypeEnv =
                  _lhsItypeEnv
              _initOtypecounter =
                  _sizeItypecounter
              _initOvarEnv =
                  _lhsIvarEnv
              ( _sizeIerrors,_sizeItp,_sizeItypecounter) =
                  size_ _sizeOerrors _sizeOexpect _sizeOtypeEnv _sizeOtypecounter _sizeOvarEnv
              ( _initIerrors,_initItp,_initItypecounter) =
                  init_ _initOerrors _initOexpect _initOtypeEnv _initOtypecounter _initOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_IntLit :: Integer ->
                   Pos ->
                   T_Expr
sem_Expr_IntLit value_ pos_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _tp =
                  INT
              _lhsOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                      then empty
                      else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_StringLit :: String ->
                      Pos ->
                      T_Expr
sem_Expr_StringLit value_ pos_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _tp =
                  STRING
              _lhsOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_While :: Pos ->
                  T_Expr ->
                  T_Expr ->
                  T_Expr
sem_Expr_While pos_ cond_ body_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _condOexpect :: TYPE
              _bodyOexpect :: TYPE
              _condOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _condOtypeEnv :: TypeEnv
              _condOtypecounter :: Int
              _condOvarEnv :: VarEnv
              _bodyOerrors :: Errors
              _bodyOtypeEnv :: TypeEnv
              _bodyOtypecounter :: Int
              _bodyOvarEnv :: VarEnv
              _condIerrors :: Errors
              _condItp :: TYPE
              _condItypecounter :: Int
              _bodyIerrors :: Errors
              _bodyItp :: TYPE
              _bodyItypecounter :: Int
              _tp =
                  VOID
              _condOexpect =
                  INT
              _bodyOexpect =
                  VOID
              _condOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                    then empty
                    else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _bodyIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _bodyItypecounter
              _condOtypeEnv =
                  _lhsItypeEnv
              _condOtypecounter =
                  _lhsItypecounter
              _condOvarEnv =
                  _lhsIvarEnv
              _bodyOerrors =
                  _condIerrors
              _bodyOtypeEnv =
                  _lhsItypeEnv
              _bodyOtypecounter =
                  _condItypecounter
              _bodyOvarEnv =
                  _lhsIvarEnv
              ( _condIerrors,_condItp,_condItypecounter) =
                  cond_ _condOerrors _condOexpect _condOtypeEnv _condOtypecounter _condOvarEnv
              ( _bodyIerrors,_bodyItp,_bodyItypecounter) =
                  body_ _bodyOerrors _bodyOexpect _bodyOtypeEnv _bodyOtypecounter _bodyOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_For :: Pos ->
                VarIdent ->
                T_Expr ->
                T_Expr ->
                T_Expr ->
                T_Expr
sem_Expr_For pos_ ident_ low_ hi_ body_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _bodyOvarEnv :: VarEnv
              _hiOexpect :: TYPE
              _lowOexpect :: TYPE
              _bodyOexpect :: TYPE
              _lowOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _lowOtypeEnv :: TypeEnv
              _lowOtypecounter :: Int
              _lowOvarEnv :: VarEnv
              _hiOerrors :: Errors
              _hiOtypeEnv :: TypeEnv
              _hiOtypecounter :: Int
              _hiOvarEnv :: VarEnv
              _bodyOerrors :: Errors
              _bodyOtypeEnv :: TypeEnv
              _bodyOtypecounter :: Int
              _lowIerrors :: Errors
              _lowItp :: TYPE
              _lowItypecounter :: Int
              _hiIerrors :: Errors
              _hiItp :: TYPE
              _hiItypecounter :: Int
              _bodyIerrors :: Errors
              _bodyItp :: TYPE
              _bodyItypecounter :: Int
              _bodyOvarEnv =
                  insertIdent ident_ (VarType LOOPCOUNTER) _lhsIvarEnv
              _tp =
                  VOID
              _hiOexpect =
                  INT
              _lowOexpect =
                  INT
              _bodyOexpect =
                  VOID
              _lowOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _bodyIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _bodyItypecounter
              _lowOtypeEnv =
                  _lhsItypeEnv
              _lowOtypecounter =
                  _lhsItypecounter
              _lowOvarEnv =
                  _lhsIvarEnv
              _hiOerrors =
                  _lowIerrors
              _hiOtypeEnv =
                  _lhsItypeEnv
              _hiOtypecounter =
                  _lowItypecounter
              _hiOvarEnv =
                  _lhsIvarEnv
              _bodyOerrors =
                  _hiIerrors
              _bodyOtypeEnv =
                  _lhsItypeEnv
              _bodyOtypecounter =
                  _hiItypecounter
              ( _lowIerrors,_lowItp,_lowItypecounter) =
                  low_ _lowOerrors _lowOexpect _lowOtypeEnv _lowOtypecounter _lowOvarEnv
              ( _hiIerrors,_hiItp,_hiItypecounter) =
                  hi_ _hiOerrors _hiOexpect _hiOtypeEnv _hiOtypecounter _hiOvarEnv
              ( _bodyIerrors,_bodyItp,_bodyItypecounter) =
                  body_ _bodyOerrors _bodyOexpect _bodyOtypeEnv _bodyOtypecounter _bodyOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_If :: Pos ->
               T_Expr ->
               T_Expr ->
               T_Expr ->
               T_Expr
sem_Expr_If pos_ cond_ thenPart_ elsePart_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _condOexpect :: TYPE
              _elsePartOexpect :: TYPE
              _thenPartOexpect :: TYPE
              _condOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _condOtypeEnv :: TypeEnv
              _condOtypecounter :: Int
              _condOvarEnv :: VarEnv
              _thenPartOerrors :: Errors
              _thenPartOtypeEnv :: TypeEnv
              _thenPartOtypecounter :: Int
              _thenPartOvarEnv :: VarEnv
              _elsePartOerrors :: Errors
              _elsePartOtypeEnv :: TypeEnv
              _elsePartOtypecounter :: Int
              _elsePartOvarEnv :: VarEnv
              _condIerrors :: Errors
              _condItp :: TYPE
              _condItypecounter :: Int
              _thenPartIerrors :: Errors
              _thenPartItp :: TYPE
              _thenPartItypecounter :: Int
              _elsePartIerrors :: Errors
              _elsePartItp :: TYPE
              _elsePartItypecounter :: Int
              _tp =
                  _expectType
              (_err,_expectType) =
                  _thenPartItp `meetErr` _elsePartItp
              _condOexpect =
                  INT
              _elsePartOexpect =
                  _expectType
              _thenPartOexpect =
                  _expectType
              _condOerrors =
                  _lhsIerrors ><
                  _err ><
                  if match _lhsIexpect _tp
                    then empty
                    else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _elsePartIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _elsePartItypecounter
              _condOtypeEnv =
                  _lhsItypeEnv
              _condOtypecounter =
                  _lhsItypecounter
              _condOvarEnv =
                  _lhsIvarEnv
              _thenPartOerrors =
                  _condIerrors
              _thenPartOtypeEnv =
                  _lhsItypeEnv
              _thenPartOtypecounter =
                  _condItypecounter
              _thenPartOvarEnv =
                  _lhsIvarEnv
              _elsePartOerrors =
                  _thenPartIerrors
              _elsePartOtypeEnv =
                  _lhsItypeEnv
              _elsePartOtypecounter =
                  _thenPartItypecounter
              _elsePartOvarEnv =
                  _lhsIvarEnv
              ( _condIerrors,_condItp,_condItypecounter) =
                  cond_ _condOerrors _condOexpect _condOtypeEnv _condOtypecounter _condOvarEnv
              ( _thenPartIerrors,_thenPartItp,_thenPartItypecounter) =
                  thenPart_ _thenPartOerrors _thenPartOexpect _thenPartOtypeEnv _thenPartOtypecounter _thenPartOvarEnv
              ( _elsePartIerrors,_elsePartItp,_elsePartItypecounter) =
                  elsePart_ _elsePartOerrors _elsePartOexpect _elsePartOtypeEnv _elsePartOtypecounter _elsePartOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Let :: Pos ->
                T_Declarations ->
                T_Expr ->
                T_Expr
sem_Expr_Let pos_ decls_ body_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOtp :: TYPE
              _bodyOexpect :: TYPE
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _declsOerrors :: Errors
              _declsOtypeEnv :: TypeEnv
              _declsOtypecounter :: Int
              _declsOvarEnv :: VarEnv
              _bodyOerrors :: Errors
              _bodyOtypeEnv :: TypeEnv
              _bodyOtypecounter :: Int
              _bodyOvarEnv :: VarEnv
              _declsIerrors :: Errors
              _declsItypeEnv :: TypeEnv
              _declsItypecounter :: Int
              _declsIvarEnv :: VarEnv
              _bodyIerrors :: Errors
              _bodyItp :: TYPE
              _bodyItypecounter :: Int
              _lhsOtp =
                  _bodyItp
              _bodyOexpect =
                  _lhsIexpect
              _lhsOerrors =
                  _bodyIerrors
              _lhsOtypecounter =
                  _bodyItypecounter
              _declsOerrors =
                  _lhsIerrors
              _declsOtypeEnv =
                  _lhsItypeEnv
              _declsOtypecounter =
                  _lhsItypecounter
              _declsOvarEnv =
                  _lhsIvarEnv
              _bodyOerrors =
                  _declsIerrors
              _bodyOtypeEnv =
                  _declsItypeEnv
              _bodyOtypecounter =
                  _declsItypecounter
              _bodyOvarEnv =
                  _declsIvarEnv
              ( _declsIerrors,_declsItypeEnv,_declsItypecounter,_declsIvarEnv) =
                  decls_ _declsOerrors _declsOtypeEnv _declsOtypecounter _declsOvarEnv
              ( _bodyIerrors,_bodyItp,_bodyItypecounter) =
                  body_ _bodyOerrors _bodyOexpect _bodyOtypeEnv _bodyOtypecounter _bodyOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Assign :: T_LValue ->
                   Pos ->
                   T_Expr ->
                   T_Expr
sem_Expr_Assign lvalue_ pos_ expr_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lvalueOexpect :: TYPE
              _exprOexpect :: TYPE
              _lvalueOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _lvalueOtypeEnv :: TypeEnv
              _lvalueOtypecounter :: Int
              _lvalueOvarEnv :: VarEnv
              _exprOerrors :: Errors
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _lvalueIerrors :: Errors
              _lvalueItp :: TYPE
              _lvalueItypecounter :: Int
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              _tp =
                  VOID
              (_err,_expType) =
                  _lvalueItp `meetErr` _exprItp
              _lvalueOexpect =
                  _expType
              _exprOexpect =
                  _expType
              _lvalueOerrors =
                  _lhsIerrors ><
                  _err ><
                  (if _lvalueItp == LOOPCOUNTER
                      then singleton (AssignLoopcounter pos_)
                      else empty
                  )   ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _exprIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _exprItypecounter
              _lvalueOtypeEnv =
                  _lhsItypeEnv
              _lvalueOtypecounter =
                  _lhsItypecounter
              _lvalueOvarEnv =
                  _lhsIvarEnv
              _exprOerrors =
                  _lvalueIerrors
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lvalueItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              ( _lvalueIerrors,_lvalueItp,_lvalueItypecounter) =
                  lvalue_ _lvalueOerrors _lvalueOexpect _lvalueOtypeEnv _lvalueOtypecounter _lvalueOvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Op :: String ->
               Pos ->
               T_Expr ->
               T_Expr ->
               T_Expr
sem_Expr_Op op_ pos_ left_ right_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _leftOexpect :: TYPE
              _rightOexpect :: TYPE
              _leftOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _leftOtypeEnv :: TypeEnv
              _leftOtypecounter :: Int
              _leftOvarEnv :: VarEnv
              _rightOerrors :: Errors
              _rightOtypeEnv :: TypeEnv
              _rightOtypecounter :: Int
              _rightOvarEnv :: VarEnv
              _leftIerrors :: Errors
              _leftItp :: TYPE
              _leftItypecounter :: Int
              _rightIerrors :: Errors
              _rightItp :: TYPE
              _rightItypecounter :: Int
              _leftOexpect =
                  _expect
              _rightOexpect =
                  _expect
              _tp =
                  INT
              (_err,_expect) =
                  let check | op_ `elem` ["+","-","*","/","|","&"] = (empty,INT)
                            | op_ `elem` [">=", "<=",  "<", ">"]   = let (e,tp) = meetErr _leftItp _rightItp
                                                                     in if tp `elem` [INT,STRING,ERROR]
                                                                           then (e,tp)
                                                                           else (e><singleton(CompareOp pos_ op_),tp)
                            | op_ `elem` [ "=", "<>"]              = let (e,tp) = meetErr _leftItp _rightItp
                                                                     in if tp == NIL
                                                                           then (e><singleton(UnknownType  pos_) ,ERROR)
                                                                           else (e,tp)
                            | otherwise  = compilerError ("unknown binary operator: " ++ op_)
                  in  check
              _leftOerrors =
                  _lhsIerrors ><
                  _err ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _rightIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _rightItypecounter
              _leftOtypeEnv =
                  _lhsItypeEnv
              _leftOtypecounter =
                  _lhsItypecounter
              _leftOvarEnv =
                  _lhsIvarEnv
              _rightOerrors =
                  _leftIerrors
              _rightOtypeEnv =
                  _lhsItypeEnv
              _rightOtypecounter =
                  _leftItypecounter
              _rightOvarEnv =
                  _lhsIvarEnv
              ( _leftIerrors,_leftItp,_leftItypecounter) =
                  left_ _leftOerrors _leftOexpect _leftOtypeEnv _leftOtypecounter _leftOvarEnv
              ( _rightIerrors,_rightItp,_rightItypecounter) =
                  right_ _rightOerrors _rightOexpect _rightOtypeEnv _rightOtypecounter _rightOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_UnOp :: Pos ->
                 String ->
                 T_Expr ->
                 T_Expr
sem_Expr_UnOp pos_ op_ expr_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _exprOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _exprOexpect :: TYPE
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              (_tp,_expect) =
                  case op_ of
                    "-" -> (INT,INT)
                    _   -> compilerError ("unknown unary operator: " ++ op_)
              _exprOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _exprIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _exprItypecounter
              _exprOexpect =
                  _expect
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lhsItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Skip :: T_Expr
sem_Expr_Skip =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _tp =
                  VOID
              _lhsOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Nil :: Pos ->
                T_Expr
sem_Expr_Nil pos_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _tp =
                  NIL
              _lhsOerrors =
                  _lhsIerrors ><
                  (if _lhsIexpect == NIL
                        then singleton (UnknownType pos_)
                        else empty
                  ) ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Break :: Pos ->
                  T_Expr
sem_Expr_Break pos_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _tp =
                  VOID
              _lhsOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_Expr_Sequence :: T_Expr ->
                     T_Expr ->
                     T_Expr
sem_Expr_Sequence left_ right_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _leftOexpect :: TYPE
              _leftOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _leftOtypeEnv :: TypeEnv
              _leftOtypecounter :: Int
              _leftOvarEnv :: VarEnv
              _rightOerrors :: Errors
              _rightOexpect :: TYPE
              _rightOtypeEnv :: TypeEnv
              _rightOtypecounter :: Int
              _rightOvarEnv :: VarEnv
              _leftIerrors :: Errors
              _leftItp :: TYPE
              _leftItypecounter :: Int
              _rightIerrors :: Errors
              _rightItp :: TYPE
              _rightItypecounter :: Int
              _tp =
                  _rightItp
              _leftOexpect =
                  _leftItp
              _leftOerrors =
                  _lhsIerrors ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _rightIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _rightItypecounter
              _leftOtypeEnv =
                  _lhsItypeEnv
              _leftOtypecounter =
                  _lhsItypecounter
              _leftOvarEnv =
                  _lhsIvarEnv
              _rightOerrors =
                  _leftIerrors
              _rightOexpect =
                  _lhsIexpect
              _rightOtypeEnv =
                  _lhsItypeEnv
              _rightOtypecounter =
                  _leftItypecounter
              _rightOvarEnv =
                  _lhsIvarEnv
              ( _leftIerrors,_leftItp,_leftItypecounter) =
                  left_ _leftOerrors _leftOexpect _leftOtypeEnv _leftOtypecounter _leftOvarEnv
              ( _rightIerrors,_rightItp,_rightItypecounter) =
                  right_ _rightOerrors _rightOexpect _rightOtypeEnv _rightOtypecounter _rightOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
-- FunDec ------------------------------------------------------
-- cata
sem_FunDec :: FunDec ->
              T_FunDec
sem_FunDec (FunDec _pos _ident _argTps _retTp _body) =
    (sem_FunDec_FunDec _pos _ident _argTps _retTp (sem_Expr _body))
-- semantic domain
type T_FunDec = Errors ->
                VarEnv ->
                TypeEnv ->
                Int ->
                VarEnv ->
                ( Errors,VarEnv,Int)
sem_FunDec_FunDec :: Pos ->
                     VarIdent ->
                     ([TypedVar]) ->
                     (Maybe TypeIdent) ->
                     T_Expr ->
                     T_FunDec
sem_FunDec_FunDec pos_ ident_ argTps_ retTp_ body_ =
    (\ _lhsIerrors
       _lhsIfundecs
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _bodyOvarEnv :: VarEnv
              _bodyOerrors :: Errors
              _bodyOexpect :: TYPE
              _lhsOerrors :: Errors
              _lhsOfundecs :: VarEnv
              _lhsOtypecounter :: Int
              _bodyOtypeEnv :: TypeEnv
              _bodyOtypecounter :: Int
              _bodyIerrors :: Errors
              _bodyItp :: TYPE
              _bodyItypecounter :: Int
              (_err1,_fundecs) =
                  case lookupPos ident_ _lhsIfundecs of
                         Just pos -> (singleton (DuplicateFun ident_ pos ), _lhsIfundecs)
                         Nothing  ->  (empty, insertIdent ident_ (FunType _atps _ret) _lhsIfundecs)
              (_err2,_argEnv,_atps) =
                  let f (TypedVar n t) ~(errs,env,tps)
                         = let (e1,tp) = findType _lhsItypeEnv t
                               (e2,en) = case lookupPos n env of
                                           Just p  -> (singleton (DuplicateArg ident_ n p), env)
                                           Nothing -> (empty, insertIdent n (VarType tp) env)
                           in(e1 >< e2 >< errs,en,tp:tps)
                  in foldr f (empty,Map.empty,[]) argTps_
              (_err3,_ret) =
                  case retTp_ of
                  Just tp -> findType _lhsItypeEnv tp
                  Nothing -> (empty,VOID)
              _bodyOvarEnv =
                  _argEnv `union` _lhsIvarEnv
              _bodyOerrors =
                  _lhsIerrors >< _err1 >< _err2 >< _err3
              _bodyOexpect =
                  _ret
              _lhsOerrors =
                  _bodyIerrors
              _lhsOfundecs =
                  _fundecs
              _lhsOtypecounter =
                  _bodyItypecounter
              _bodyOtypeEnv =
                  _lhsItypeEnv
              _bodyOtypecounter =
                  _lhsItypecounter
              ( _bodyIerrors,_bodyItp,_bodyItypecounter) =
                  body_ _bodyOerrors _bodyOexpect _bodyOtypeEnv _bodyOtypecounter _bodyOvarEnv
          in  ( _lhsOerrors,_lhsOfundecs,_lhsOtypecounter)))
-- FunDecs -----------------------------------------------------
-- cata
sem_FunDecs :: FunDecs ->
               T_FunDecs
sem_FunDecs list =
    (Prelude.foldr sem_FunDecs_Cons sem_FunDecs_Nil (Prelude.map sem_FunDec list))
-- semantic domain
type T_FunDecs = Errors ->
                 TypeEnv ->
                 Int ->
                 VarEnv ->
                 ( Errors,VarEnv,Int)
sem_FunDecs_Cons :: T_FunDec ->
                    T_FunDecs ->
                    T_FunDecs
sem_FunDecs_Cons hd_ tl_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOfundecs :: VarEnv
              _hdOfundecs :: VarEnv
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _hdOerrors :: Errors
              _hdOtypeEnv :: TypeEnv
              _hdOtypecounter :: Int
              _hdOvarEnv :: VarEnv
              _tlOerrors :: Errors
              _tlOtypeEnv :: TypeEnv
              _tlOtypecounter :: Int
              _tlOvarEnv :: VarEnv
              _hdIerrors :: Errors
              _hdIfundecs :: VarEnv
              _hdItypecounter :: Int
              _tlIerrors :: Errors
              _tlIfundecs :: VarEnv
              _tlItypecounter :: Int
              _lhsOfundecs =
                  _hdIfundecs
              _hdOfundecs =
                  _tlIfundecs
              _lhsOerrors =
                  _tlIerrors
              _lhsOtypecounter =
                  _tlItypecounter
              _hdOerrors =
                  _lhsIerrors
              _hdOtypeEnv =
                  _lhsItypeEnv
              _hdOtypecounter =
                  _lhsItypecounter
              _hdOvarEnv =
                  _lhsIvarEnv
              _tlOerrors =
                  _hdIerrors
              _tlOtypeEnv =
                  _lhsItypeEnv
              _tlOtypecounter =
                  _hdItypecounter
              _tlOvarEnv =
                  _lhsIvarEnv
              ( _hdIerrors,_hdIfundecs,_hdItypecounter) =
                  hd_ _hdOerrors _hdOfundecs _hdOtypeEnv _hdOtypecounter _hdOvarEnv
              ( _tlIerrors,_tlIfundecs,_tlItypecounter) =
                  tl_ _tlOerrors _tlOtypeEnv _tlOtypecounter _tlOvarEnv
          in  ( _lhsOerrors,_lhsOfundecs,_lhsOtypecounter)))
sem_FunDecs_Nil :: T_FunDecs
sem_FunDecs_Nil =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOfundecs :: VarEnv
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _lhsOfundecs =
                  Map.empty
              _lhsOerrors =
                  _lhsIerrors
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOfundecs,_lhsOtypecounter)))
-- LValue ------------------------------------------------------
-- cata
sem_LValue :: LValue ->
              T_LValue
sem_LValue (Sub _pos _expr _index) =
    (sem_LValue_Sub _pos (sem_LValue _expr) (sem_Expr _index))
sem_LValue (Dot _pos _expr _ident) =
    (sem_LValue_Dot _pos (sem_LValue _expr) _ident)
sem_LValue (Ident _ident) =
    (sem_LValue_Ident _ident)
-- semantic domain
type T_LValue = Errors ->
                TYPE ->
                TypeEnv ->
                Int ->
                VarEnv ->
                ( Errors,TYPE,Int)
sem_LValue_Sub :: Pos ->
                  T_LValue ->
                  T_Expr ->
                  T_LValue
sem_LValue_Sub pos_ expr_ index_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _indexOexpect :: TYPE
              _exprOexpect :: TYPE
              _exprOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _indexOerrors :: Errors
              _indexOtypeEnv :: TypeEnv
              _indexOtypecounter :: Int
              _indexOvarEnv :: VarEnv
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              _indexIerrors :: Errors
              _indexItp :: TYPE
              _indexItypecounter :: Int
              (_err,_tp) =
                  arrayComponentType pos_ _exprItp
              _indexOexpect =
                  INT
              _exprOexpect =
                  case _tp of ERROR -> ERROR ; _ -> _exprItp
              _exprOerrors =
                  _lhsIerrors ><
                  _err ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _indexIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _indexItypecounter
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lhsItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              _indexOerrors =
                  _exprIerrors
              _indexOtypeEnv =
                  _lhsItypeEnv
              _indexOtypecounter =
                  _exprItypecounter
              _indexOvarEnv =
                  _lhsIvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
              ( _indexIerrors,_indexItp,_indexItypecounter) =
                  index_ _indexOerrors _indexOexpect _indexOtypeEnv _indexOtypecounter _indexOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_LValue_Dot :: Pos ->
                  T_LValue ->
                  VarIdent ->
                  T_LValue
sem_LValue_Dot pos_ expr_ ident_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _exprOexpect :: TYPE
              _exprOerrors :: Errors
              _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              _exprOtypeEnv :: TypeEnv
              _exprOtypecounter :: Int
              _exprOvarEnv :: VarEnv
              _exprIerrors :: Errors
              _exprItp :: TYPE
              _exprItypecounter :: Int
              (_err1,_fieldEnv) =
                  recordType pos_ _exprItp
              (_err2,_tp) =
                  recordFieldType pos_ _fieldEnv ident_
              _exprOexpect =
                  case _tp of ERROR -> ERROR ; _ -> _exprItp
              _exprOerrors =
                  _lhsIerrors ><
                  _err1 ><
                  _err2 ><
                  if match _lhsIexpect _tp
                     then empty
                     else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOerrors =
                  _exprIerrors
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _exprItypecounter
              _exprOtypeEnv =
                  _lhsItypeEnv
              _exprOtypecounter =
                  _lhsItypecounter
              _exprOvarEnv =
                  _lhsIvarEnv
              ( _exprIerrors,_exprItp,_exprItypecounter) =
                  expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
sem_LValue_Ident :: VarIdent ->
                    T_LValue
sem_LValue_Ident ident_ =
    (\ _lhsIerrors
       _lhsIexpect
       _lhsItypeEnv
       _lhsItypecounter
       _lhsIvarEnv ->
         (let _lhsOerrors :: Errors
              _lhsOtp :: TYPE
              _lhsOtypecounter :: Int
              (_errs,_tp) =
                  findVar _lhsIvarEnv ident_
              _lhsOerrors =
                  _lhsIerrors ><
                  _errs ><
                  if match _lhsIexpect _tp
                      then empty
                      else singleton (TypeMisMatch  _lhsIexpect _tp)
              _lhsOtp =
                  _tp
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtp,_lhsOtypecounter)))
-- Program -----------------------------------------------------
-- cata
sem_Program :: Program ->
               T_Program
sem_Program (Program _expr) =
    (sem_Program_Program (sem_Expr _expr))
-- semantic domain
type T_Program = ( ([Error]))
sem_Program_Program :: T_Expr ->
                       T_Program
sem_Program_Program expr_ =
    (let _lhsOerrors :: ([Error])
         _exprOerrors :: Errors
         _exprOvarEnv :: VarEnv
         _exprOtypeEnv :: TypeEnv
         _exprOtypecounter :: Int
         _exprOexpect :: TYPE
         _exprIerrors :: Errors
         _exprItp :: TYPE
         _exprItypecounter :: Int
         _lhsOerrors =
             toList _exprIerrors
         _exprOerrors =
             empty
         _exprOvarEnv =
             initVarEnv
         _exprOtypeEnv =
             initTypeEnv
         _exprOtypecounter =
             10
         _exprOexpect =
             _exprItp
         ( _exprIerrors,_exprItp,_exprItypecounter) =
             expr_ _exprOerrors _exprOexpect _exprOtypeEnv _exprOtypecounter _exprOvarEnv
     in  ( _lhsOerrors))
-- TypeDec -----------------------------------------------------
-- cata
sem_TypeDec :: TypeDec ->
               T_TypeDec
sem_TypeDec (TypeDec _pos _ident _tp) =
    (sem_TypeDec_TypeDec _pos _ident _tp)
-- semantic domain
type T_TypeDec = Errors ->
                 TypeEnv ->
                 Int ->
                 ((TypeEnv, TypeSyns)) ->
                 ( Errors,Int,((TypeEnv, TypeSyns)))
sem_TypeDec_TypeDec :: Pos ->
                       TypeIdent ->
                       Type ->
                       T_TypeDec
sem_TypeDec_TypeDec pos_ ident_ tp_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter
       _lhsItypedecs ->
         (let _lhsOtypecounter :: Int
              _lhsOerrors :: Errors
              _lhsOtypedecs :: ((TypeEnv, TypeSyns))
              (_errs,_typedecs) =
                  let (env,syns) = _lhsItypedecs
                  in case lookupPos ident_ env `mplus` lookupPos  ident_ syns of
                       Just pos -> (singleton (DuplicateType ident_ pos ), _lhsItypedecs)
                       Nothing  ->  case tp_ of
                                     Var nm   ->  (empty, (env, insertIdent ident_ nm syns) )
                                     Array t  ->  let (err,t')   = findType _lhsItypeEnv t
                                                      tp         = ARRAY ident_ _lhsItypecounter t'
                                                  in (err, (insertIdent ident_ tp env, syns))
                                     Record fs -> let (err,fs')  = recordFields _lhsItypeEnv fs
                                                      tp         = RECORD ident_ _lhsItypecounter fs'
                                                  in (err, (insertIdent ident_ tp env, syns))
              _lhsOtypecounter =
                  _lhsItypecounter + 1
              _lhsOerrors =
                  _lhsIerrors >< _errs
              _lhsOtypedecs =
                  _typedecs
          in  ( _lhsOerrors,_lhsOtypecounter,_lhsOtypedecs)))
-- TypeDecs ----------------------------------------------------
-- cata
sem_TypeDecs :: TypeDecs ->
                T_TypeDecs
sem_TypeDecs list =
    (Prelude.foldr sem_TypeDecs_Cons sem_TypeDecs_Nil (Prelude.map sem_TypeDec list))
-- semantic domain
type T_TypeDecs = Errors ->
                  TypeEnv ->
                  Int ->
                  ( Errors,Int,((TypeEnv, TypeSyns)))
sem_TypeDecs_Cons :: T_TypeDec ->
                     T_TypeDecs ->
                     T_TypeDecs
sem_TypeDecs_Cons hd_ tl_ =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter ->
         (let _lhsOtypedecs :: ((TypeEnv, TypeSyns))
              _hdOtypedecs :: ((TypeEnv, TypeSyns))
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _hdOerrors :: Errors
              _hdOtypeEnv :: TypeEnv
              _hdOtypecounter :: Int
              _tlOerrors :: Errors
              _tlOtypeEnv :: TypeEnv
              _tlOtypecounter :: Int
              _hdIerrors :: Errors
              _hdItypecounter :: Int
              _hdItypedecs :: ((TypeEnv, TypeSyns))
              _tlIerrors :: Errors
              _tlItypecounter :: Int
              _tlItypedecs :: ((TypeEnv, TypeSyns))
              _lhsOtypedecs =
                  _hdItypedecs
              _hdOtypedecs =
                  _tlItypedecs
              _lhsOerrors =
                  _tlIerrors
              _lhsOtypecounter =
                  _tlItypecounter
              _hdOerrors =
                  _lhsIerrors
              _hdOtypeEnv =
                  _lhsItypeEnv
              _hdOtypecounter =
                  _lhsItypecounter
              _tlOerrors =
                  _hdIerrors
              _tlOtypeEnv =
                  _lhsItypeEnv
              _tlOtypecounter =
                  _hdItypecounter
              ( _hdIerrors,_hdItypecounter,_hdItypedecs) =
                  hd_ _hdOerrors _hdOtypeEnv _hdOtypecounter _hdOtypedecs
              ( _tlIerrors,_tlItypecounter,_tlItypedecs) =
                  tl_ _tlOerrors _tlOtypeEnv _tlOtypecounter
          in  ( _lhsOerrors,_lhsOtypecounter,_lhsOtypedecs)))
sem_TypeDecs_Nil :: T_TypeDecs
sem_TypeDecs_Nil =
    (\ _lhsIerrors
       _lhsItypeEnv
       _lhsItypecounter ->
         (let _lhsOtypedecs :: ((TypeEnv, TypeSyns))
              _lhsOerrors :: Errors
              _lhsOtypecounter :: Int
              _lhsOtypedecs =
                  (Map.empty,Map.empty)
              _lhsOerrors =
                  _lhsIerrors
              _lhsOtypecounter =
                  _lhsItypecounter
          in  ( _lhsOerrors,_lhsOtypecounter,_lhsOtypedecs)))