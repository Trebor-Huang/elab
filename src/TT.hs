module TT where
import ABT
import Control.Monad.State
import Data.Set (Set, union, singleton, empty)
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

allConstants :: Term -> Set ConstName
allConstants (Node (m :-> n)) = allConstants m `union` allConstants n
allConstants (Node (Const c)) = singleton c
allConstants (Node (App m n)) = undefined
allConstants (Node (Lam m)) = allConstants m
allConstants (Bind t) = allConstants t
allConstants _ = empty

hasDuplicate :: (Eq a) => [a] -> Bool
hasDuplicate [] = False
hasDuplicate (x:xs) = x `elem` xs && hasDuplicate xs

type Context = [(VarName, Type)]  -- ! Check distinctness
contextDistinct :: Context -> Bool
contextDistinct = hasDuplicate . map fst

data SignatureSnippet =
      DeclareType ConstName Type
    | DeclareEq ConstName Type Term
    | DeclareConstraint ConstName Type Term [Constraint] -- New
type Signature = [SignatureSnippet]
signatureDistinct :: Signature -> Bool
signatureDistinct = hasDuplicate . map getName

getName (DeclareType c _) = c
getName (DeclareEq c _ _) = c
getName (DeclareConstraint c _ _ _) = c

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

type Elab a = State Signature a -- TODO error report; currently just crashes
addMeta :: ConstName -> Type -> Elab ()
addMeta c t = do
    s <- get
    if c `elem` map getName s then
        error $ "Non-unique name " ++ c
    else
        put $ DeclareType c t : s

addAssignment :: ConstName -> Term -> Elab ()
addAssignment c t = do
    s <- get
    let (p, DeclareType c' t' : q) = break ((c ==) . getName) s
    put (p ++ DeclareEq c t' t : q)

addConst :: ConstName -> Type -> Term -> [Constraint] -> Elab ()
addConst c ty tm cs = do
    s <- get
    if c `elem` map getName s then
        error $ "Non-unique name " ++ c
    else
        put $ DeclareConstraint c ty tm cs : s

inScope :: ConstName -> Term -> Elab ()
inScope c t = do
    s <- get
    let (p, DeclareType _ t' : q) = break ((c ==) . getName) s
    if all (`elem` map getName p) (toList $ allConstants t) then
        return
    else
        error "Out of scope"
