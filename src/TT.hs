module TT where
import ABT
import Control.Monad.State
import Data.Set (Set, union, singleton, empty, toList, fromList)
type ConstName = String
-- If terms and types are mutually recursively defined, the ABTCompatible class needs
-- to use the forall extension. For simplicity, we define a big type containing both.
data Term' = Set
    | (:->) Term Term
    | Const ConstName
    | App Term Term
    | Lam Term
    deriving (Show, Eq, Ord)
type Term = ABT Term'
type Type = Term
instance (ABTCompatible Term') where
    fallthrough f (m :-> n) = f m :-> f n
    fallthrough f (App m n) = App (f m) (f n)
    fallthrough f (Lam n) = Lam (f n)
    fallthrough _ a = a

    collect f (m :-> n) = fromList [f m, f n]
    collect f (App m n) = fromList [f m, f n]
    collect f (Lam n) = singleton $ f n
    collect _ m = empty

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
type Telescope = Context
-- Telescopes are cons, Contexts are snoc

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

getType (DeclareType _ t) = t
getType (DeclareEq _ t _) = t
getType (DeclareConstraint _ t _ _) = t

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
    | UApp UserExpr UserExpr -- ! No beta allowed
    | UConst ConstName
    | USet
    | UFun UserExpr UserExpr
    | Unknown
type UserExpr = ABT UserExpr'

instance (ABTCompatible UserExpr') where
    fallthrough f (ULam x) = ULam $ f x
    fallthrough f (UApp x y) = UApp (f x) (f y)
    fallthrough f (UFun x y) = UFun (f x) (f y)
    fallthrough f x = x

    collect f (ULam x) = singleton $ f x
    collect f (UApp x y) = fromList [f x, f y]
    collect f (UFun x y) = fromList [f x, f y]
    collect f _ = empty

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
        return ()
    else
        error "Out of scope"

lookUp :: ConstName -> Elab Type
lookUp c = gets (getType . head . filter ((== c).getName))

checkType :: Context -> UserExpr -> Elab Type
checkType ctx (Node USet) = return (Node Set)
checkType ctx (Node (UFun e1 (Bind e2))) = do
    t1 <- checkType ctx e1
    let x = fresh [e1, e2]
    t2 <- checkType ((x, t1) : ctx) (instantiate (FVar x) e2)
    return $ Node (t1 :-> Bind (abstract x t2))
checkType ctx e = checkTerm ctx e (Node Set)

checkTerm :: Context -> UserExpr -> Type -> Elab Term
checkTerm ctx e t = undefined

inferType :: Context -> UserExpr -> Elab (Type, Term)
inferType ctx e = undefined

checkTypeConversion :: Context -> Type -> Type -> Elab [Constraint]
checkTypeConversion = undefined

checkTermConversion :: Context -> Type -> Term -> Term -> Elab [Constraint]
checkTermConversion = undefined

stripGuardedConstant :: Signature -> Signature
stripGuardedConstant = undefined
