

-- UUAGC 0.9.57 (TigerError.ag)
module TigerError where


import TigerTypes
import UU.Scanner.Position

  
showField ident = show (getName ident)  
-- Error -------------------------------------------------------
data Error = UndeclaredVar (Ident)
           | UndeclaredType (Ident)
           | DuplicateType (Ident) (Pos)
           | DuplicateFun (Ident) (Pos)
           | DuplicateArg (Ident) (Ident) (Pos)
           | DupRecordFieldDecl (Ident) (Pos)
           | CyclicType (Ident)
           | UnknownType (Pos)
           | NotVarType (Ident)
           | UndeclaredFun (Ident)
           | NotFunType (Ident)
           | NotArrayType (Pos)
           | NotRecordType (Pos)
           | NoSuchField (Pos) (Ident)
           | TypeMisMatch (TYPE) (TYPE)
           | TooManyArguments (Ident)
           | TooFewArguments (Ident)
           | FieldNotInit (Ident)
           | CompareOp (Pos) (String)
           | AssignLoopcounter (Pos)
           | InitWithVoid (Pos)
-- cata
sem_Error :: Error ->
             T_Error
sem_Error (UndeclaredVar _ident) =
    (sem_Error_UndeclaredVar _ident)
sem_Error (UndeclaredType _ident) =
    (sem_Error_UndeclaredType _ident)
sem_Error (DuplicateType _ident _pos2) =
    (sem_Error_DuplicateType _ident _pos2)
sem_Error (DuplicateFun _ident _pos2) =
    (sem_Error_DuplicateFun _ident _pos2)
sem_Error (DuplicateArg _fun _ident _pos2) =
    (sem_Error_DuplicateArg _fun _ident _pos2)
sem_Error (DupRecordFieldDecl _ident _pos2) =
    (sem_Error_DupRecordFieldDecl _ident _pos2)
sem_Error (CyclicType _ident) =
    (sem_Error_CyclicType _ident)
sem_Error (UnknownType _pos) =
    (sem_Error_UnknownType _pos)
sem_Error (NotVarType _ident) =
    (sem_Error_NotVarType _ident)
sem_Error (UndeclaredFun _ident) =
    (sem_Error_UndeclaredFun _ident)
sem_Error (NotFunType _ident) =
    (sem_Error_NotFunType _ident)
sem_Error (NotArrayType _pos) =
    (sem_Error_NotArrayType _pos)
sem_Error (NotRecordType _pos) =
    (sem_Error_NotRecordType _pos)
sem_Error (NoSuchField _pos _field) =
    (sem_Error_NoSuchField _pos _field)
sem_Error (TypeMisMatch _expect _tp) =
    (sem_Error_TypeMisMatch _expect _tp)
sem_Error (TooManyArguments _fun) =
    (sem_Error_TooManyArguments _fun)
sem_Error (TooFewArguments _fun) =
    (sem_Error_TooFewArguments _fun)
sem_Error (FieldNotInit _field) =
    (sem_Error_FieldNotInit _field)
sem_Error (CompareOp _pos _op) =
    (sem_Error_CompareOp _pos _op)
sem_Error (AssignLoopcounter _pos) =
    (sem_Error_AssignLoopcounter _pos)
sem_Error (InitWithVoid _pos) =
    (sem_Error_InitWithVoid _pos)
-- semantic domain
type T_Error = ( String)
sem_Error_UndeclaredVar :: Ident ->
                           T_Error
sem_Error_UndeclaredVar ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "undeclared variable: " ++ show ident_
     in  ( _lhsOmsg))
sem_Error_UndeclaredType :: Ident ->
                            T_Error
sem_Error_UndeclaredType ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "undeclared type: " ++ show ident_
     in  ( _lhsOmsg))
sem_Error_DuplicateType :: Ident ->
                           Pos ->
                           T_Error
sem_Error_DuplicateType ident_ pos2_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "duplicate type declaration: " ++ show ident_ ++ " other occurrence at: " ++ show pos2_
     in  ( _lhsOmsg))
sem_Error_DuplicateFun :: Ident ->
                          Pos ->
                          T_Error
sem_Error_DuplicateFun ident_ pos2_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "duplicate function declaration: " ++ show ident_ ++ " other occurrence at: " ++ show pos2_
     in  ( _lhsOmsg))
sem_Error_DuplicateArg :: Ident ->
                          Ident ->
                          Pos ->
                          T_Error
sem_Error_DuplicateArg fun_ ident_ pos2_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "duplicate formal argument declaration: " ++ show ident_ ++ " other occurrence at: " ++ show pos2_
     in  ( _lhsOmsg))
sem_Error_DupRecordFieldDecl :: Ident ->
                                Pos ->
                                T_Error
sem_Error_DupRecordFieldDecl ident_ pos2_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "duplicate record field declaration: " ++ show ident_ ++ " other occurrence at: " ++ show pos2_
     in  ( _lhsOmsg))
sem_Error_CyclicType :: Ident ->
                        T_Error
sem_Error_CyclicType ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "cyclic type synonym: " ++ show ident_
     in  ( _lhsOmsg))
sem_Error_UnknownType :: Pos ->
                         T_Error
sem_Error_UnknownType pos_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "unable to determine type for expression at: " ++ show pos_
     in  ( _lhsOmsg))
sem_Error_NotVarType :: Ident ->
                        T_Error
sem_Error_NotVarType ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "identifier: " ++ show ident_ ++ " is not a variable"
     in  ( _lhsOmsg))
sem_Error_UndeclaredFun :: Ident ->
                           T_Error
sem_Error_UndeclaredFun ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "undeclared function: " ++ show ident_
     in  ( _lhsOmsg))
sem_Error_NotFunType :: Ident ->
                        T_Error
sem_Error_NotFunType ident_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "identifier: " ++ show ident_ ++ " is not a function"
     in  ( _lhsOmsg))
sem_Error_NotArrayType :: Pos ->
                          T_Error
sem_Error_NotArrayType pos_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ " subscript of non-array type"
     in  ( _lhsOmsg))
sem_Error_NotRecordType :: Pos ->
                           T_Error
sem_Error_NotRecordType pos_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ " field selection of non-record type"
     in  ( _lhsOmsg))
sem_Error_NoSuchField :: Pos ->
                         Ident ->
                         T_Error
sem_Error_NoSuchField pos_ field_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ " record type  does not have a field named: " ++ showField field_
     in  ( _lhsOmsg))
sem_Error_TypeMisMatch :: TYPE ->
                          TYPE ->
                          T_Error
sem_Error_TypeMisMatch expect_ tp_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "type: " ++ show tp_ ++ " does not match: " ++ show expect_
     in  ( _lhsOmsg))
sem_Error_TooManyArguments :: Ident ->
                              T_Error
sem_Error_TooManyArguments fun_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "too many arguments for: " ++ show fun_
     in  ( _lhsOmsg))
sem_Error_TooFewArguments :: Ident ->
                             T_Error
sem_Error_TooFewArguments fun_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "not enough arguments for: " ++ show fun_
     in  ( _lhsOmsg))
sem_Error_FieldNotInit :: Ident ->
                          T_Error
sem_Error_FieldNotInit field_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "field not initialized: " ++ showField field_
     in  ( _lhsOmsg))
sem_Error_CompareOp :: Pos ->
                       String ->
                       T_Error
sem_Error_CompareOp pos_ op_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ ":" ++ " operator " ++ show op_ ++ " only defined for int and string"
     in  ( _lhsOmsg))
sem_Error_AssignLoopcounter :: Pos ->
                               T_Error
sem_Error_AssignLoopcounter pos_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ ":" ++ "cannot assign to loop variable"
     in  ( _lhsOmsg))
sem_Error_InitWithVoid :: Pos ->
                          T_Error
sem_Error_InitWithVoid pos_ =
    (let _lhsOmsg :: String
         _lhsOmsg =
             "at: " ++ show pos_ ++ ":" ++ "cannot initialize with no value"
     in  ( _lhsOmsg))