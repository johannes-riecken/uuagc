{-# LANGUAGE OverloadedStrings #-}
module TigerPretty where
import TigerASS
import Test.Hspec
import Prettyprinter
import Hedgehog


instance Pretty Program where
    pretty (Program e) = pretty e

instance Pretty Ident where
    pretty (Id x) = pretty x

sw = 4

instance Pretty Expr where
    pretty (LValue x) = pretty x
    pretty (Apply v []) = pretty v <> "()"
    pretty (Apply v args) = pretty v <> parens (foldr1 (surround ", ") . map pretty $ args)
    pretty (RecordVal x ys) = pretty x <> "{" <> (foldr1 (surround ", ") . map pretty $ ys) <> "}"
    pretty (ArrayVal ty e0 e1) = pretty ty <+> "[" <+> pretty e0 <+> "]" <+> "of" <+> pretty e1
    pretty (For v e0 e1 e2) = "for" <+> pretty v <+> ":=" <+> pretty e0 <+> "to" <+> pretty e1 <> line <> "do" <+> pretty e2
    -- Is that a bug in the parser?
    pretty (Op x@"<" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@"<=" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@"=" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@">" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@">=" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x@"<>" r l) = pretty l <+> pretty x <+> pretty r
    pretty (Op x l r) = pretty l <+> pretty x <+> pretty r
    pretty (UnOp x e) = pretty x <> pretty e
    pretty (If e0 e1 Skip) = nest sw . vsep $ ["if" <+> pretty e0, "then" <+> pretty e1]
    pretty (If e0 e1 e2) = nest sw . vsep $ ["if" <+> pretty e0, "then" <+> pretty e1, "else" <+> pretty e2]
    pretty (Let ds e) = vsep ["let", indent sw . parSep . map pretty $ ds, "in", indent sw . pretty $ e, "end"]
    pretty (Assign v e) = pretty v <+> ":=" <+> pretty e
    pretty (IntLit x) = pretty x
    pretty (StringLit x) = pretty x
    pretty (While cond body) = nest sw . vsep $ ["while" <+> pretty cond, "do" <+> pretty body]
    pretty Skip = "()"
    pretty Nil = "nil"
    pretty x@(Sequence e0 e1) = lparen <> line <> indent sw (prettySeq x) <> line <> rparen
    pretty x = error ("missing pretty: " <> show x)

-- Two hard line breaks = blank line between paragraphs
parSep :: [Doc ann] -> Doc ann
parSep = concatWith (\x y -> x <> hardline <> hardline <> y)

prettySeq (Sequence e0 e1@(Sequence _ _)) = pretty e0 <> ";" <> line <> prettySeq e1
prettySeq (Sequence e0 e1) = pretty e0 <> ";" <> line <> pretty e1

instance Pretty AssignField where
    pretty (AssignField x y) = pretty x <+> "=" <+> pretty y

instance Pretty FunDec where
    pretty (FunDec nm args Nothing body) = nest sw $ vsep ["function" <+> pretty nm <> parens (concatWith (surround ", ") $ map pretty args) <+> "=", pretty body]
    pretty (FunDec nm args (Just ret) body) = nest sw $ vsep ["function" <+> pretty nm <> parens (concatWith (surround ", ") $ map pretty args) <+> ":" <+> pretty ret <+> "=", pretty body]

instance Pretty DeclGroup where
    pretty (VarDec x Nothing e) = "var" <+> pretty x <+> ":=" <+> pretty e
    pretty (FunDecs x) = parSep . map pretty $ x
    pretty (TypeDecs x) = vsep . map pretty $ x
    pretty x = error ("missing pretty: " <> show x)

instance Pretty TypeDec where
    pretty (TypeDec nm ty) = "type" <+> pretty nm <+> "=" <+> (pretty $ ty)

instance Pretty Type where
    pretty (Array ty) = "array" <+> "of" <+> pretty ty
    pretty (Record tys) = braces . foldr1 (surround ", ") . map pretty $ tys
    pretty x = error ("missing pretty: " <> show x)

instance Pretty LValue where
    pretty (Sub lv e0) = pretty lv <> "[" <> pretty e0 <> "]"
    pretty (Dot lv nm1) = pretty lv <> "." <> pretty nm1
    pretty (Ident x) = pretty x

instance Pretty TypedVar where
    pretty (TypedVar v t) = pretty v <+> ":" <+> pretty t


