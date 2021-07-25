module TT where
import ABT
type ConstName = String
-- If terms and types are mutually recursively defined, the ABTCompatible class needs
-- to use the forall extension. For simplicity, we define a big type containing both.
data Term' = Set 
    | (:->) Term Term
    | Const ConstName 
    | App Term Term
    | Lam Term
    deriving (Show, Eq)
type Term = ABT Term'
type Type = Term
instance (ABTCompatible Term') where
    fallthrough f (m :-> n) = f m :-> f n
    fallthrough f (App m n) = App (f m) (f n)
    fallthrough f (Lam n) = Lam (f n)
    fallthrough _ a = a

type Context = [(VarName, Type)]  -- ! Check distinctness
data SignatureSnippet = 
      DeclareType ConstName Type 
    | DeclareEq ConstName Type Term 
    | DeclareConstraint ConstName Type Term Constraint -- New
type Signature = [SignatureSnippet]

data Judgement =
      Sig Signature
    | Ctx Signature Context
    | Typ Signature Context Type
    | Trm Signature Context Type Term
    | EqTyp Signature Context Type Type
    | EqTrm Signature Context Type Term Term

data Constraint = 
      CTyp Context Type Type
    | CTrm Context Type Term Term
    | CTms Context [(Term, Term, Type)]

data UserExpr' =
      ULam UserExpr
    | UApp UserExpr  -- ! No beta allowed
    | USet
    | UFun UserExpr UserExpr
    | Unknown
type UserExpr = ABT UserExpr'


