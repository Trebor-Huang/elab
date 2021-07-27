module TT where
import ABT
import Control.Monad.State ( gets, MonadState(get, put), State )
import Data.Set (Set, union, unions, singleton, empty, toList, fromList)
import Data.Maybe (fromJust)
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
allConstants (Node (App m n)) = allConstants m `union` allConstants n
allConstants (Node (Lam m)) = allConstants m
allConstants (Bind t) = allConstants t
allConstants _ = empty

hasDuplicate :: (Eq a) => [a] -> Bool
hasDuplicate [] = False
hasDuplicate (x:xs) = x `elem` xs && hasDuplicate xs

type Context = [(VarName, Type)]  -- ! Check distinctness
type Telescope = Context
-- Telescopes are cons, Contexts are snoc

-- The following aux functions implement
-- shorthands like "Gamma -> A", "f Gamma", representing
-- iterated function spaces and function application
funcContext :: Context -> Type -> Type
funcContext [] t = t
funcContext ((x, m):xs) t = funcContext xs (Node (m :-> abstract x t))

appContext :: Term -> Context -> Term
appContext t [] = t
appContext t ((x, _):xs) = Node (App (appContext t xs) (FVar x))

lamContext :: Context -> Term -> Term
lamContext [] t = t
lamContext ((x, m):xs) t = lamContext xs $ Node $ Lam $ abstract x t

funcTelescope :: Telescope -> Type -> Type
funcTelescope [] t = t
funcTelescope ((x, m):xs) t = Node (m :-> abstract x (funcTelescope xs t))

appTelescope :: Term -> Telescope -> Term
appTelescope t [] = t
appTelescope t ((x, _): xs) = appTelescope (Node $ App t $ FVar x) xs

lamTelescope :: Telescope -> Term -> Term
lamTelescope [] t = t
lamTelescope ((x, m):xs) t = Node $ Lam $ abstract x $ lamTelescope xs t

contextDistinct :: Context -> Bool
contextDistinct = hasDuplicate . map fst

data SignatureSnippet =
      DeclareType ConstName Type
    | DeclareEq ConstName Type Term
    | DeclareConstraint ConstName Type Term [Constraint] -- New
type Signature = [SignatureSnippet]
signatureDistinct :: Signature -> Bool
signatureDistinct = hasDuplicate . map getName

getName :: SignatureSnippet -> ConstName
getName (DeclareType c _) = c
getName (DeclareEq c _ _) = c
getName (DeclareConstraint c _ _ _) = c

getType :: SignatureSnippet -> Type
getType (DeclareType _ t) = t
getType (DeclareEq _ t _) = t
getType (DeclareConstraint _ t _ _) = t

constants = "c" : map ('`' :) constants
freshConstant :: Signature -> ConstName
freshConstant s = head $ filter (`notElem` map getName s) constants

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

lookUpConstant :: ConstName -> Elab Type
lookUpConstant c = gets (getType . head . filter ((== c).getName))

checkType :: Context -> UserExpr -> Elab Type
checkType ctx (Node USet) = return (Node Set)
checkType ctx (Node (UFun e1 (Bind e2))) = do
    t1 <- checkType ctx e1
    let x = fresh [e1, e2] (map fst ctx)
    t2 <- checkType ((x, t1) : ctx) (instantiate (FVar x) e2)
    return $ Node (t1 :-> Bind (abstract x t2))
checkType ctx e = checkTerm ctx e (Node Set)

checkTerm :: Context -> UserExpr -> Type -> Elab Term
checkTerm ctx (Node (ULam (Bind e))) (Node (a :-> (Bind b))) = do
    let x = fresh' (unions [freeVariables e, freeVariables a, freeVariables b])
    Node . Lam . Bind . abstract x <$>
      checkTerm ((x, a) : ctx) (instantiate (FVar x) e) (instantiate (FVar x) b)
checkTerm ctx (Node Unknown) t = do
    c <- gets freshConstant
    addMeta c (funcContext ctx t)
    return (appContext (Node (Const c)) ctx)
checkTerm ctx e t = do
    (t', s) <- inferType ctx e
    constraints <- checkTypeConversion ctx t t'
    if null constraints then
        return s
    else do
        p <- gets freshConstant
        addConst p (funcContext ctx t) (lamContext ctx s) constraints
        return (appContext (Node (Const p)) ctx)

inferType :: Context -> UserExpr -> Elab (Type, Term)
inferType ctx (FVar x) = return (fromJust $ lookup x ctx, FVar x)
inferType ctx (Node (UConst c)) = do
    s <- lookUpConstant c
    return (s, Node (Const c))
inferType ctx (Node (UApp m n)) = do
    x <- inferType ctx m
    let (Node (t1 :-> t2), s) = x
    t <- checkTerm ctx n t1
    return (instantiate t t2, Node (App s t))
inferType ctx _ = error "Can't infer"

checkTypeConversion :: Context -> Type -> Type -> Elab [Constraint]
checkTypeConversion ctx (Node Set) (Node Set) = return []
checkTypeConversion ctx (Node (a1 :-> (Bind b1))) (Node (a2 :-> (Bind b2))) 
    = do
        constraints <- checkTypeConversion ctx a1 a2
        let x = fresh [a1, a2, b1, b2] (map fst ctx)
        if null constraints then do
            checkTypeConversion ((x, a1):ctx) (instantiate (FVar x) b1) (instantiate (FVar x) b2)
        else do
            p <- gets freshConstant
            addConst p
                (funcContext ctx $ Node (a1 :-> a2))
                (lamContext ctx $ Node (Lam (Bind (BVar 0))))
                constraints
            constraints' <- checkTypeConversion ((x, a1):ctx)
                (instantiate (Node (App (appContext (Node (Const p)) ctx) (FVar x))) b1)
                (instantiate (Node (App (appContext (Node (Const p)) ctx) (FVar x))) b2)
            return $ constraints ++ constraints'
checkTypeConversion ctx t1 t2 = checkTermConversion ctx (Node Set) t1 t2

checkTermConversion :: Context -> Type -> Term -> Term -> Elab [Constraint]
-- This one needs backtracking now
checkTermConversion = undefined

checkWHNFConversion :: Context -> Type -> Term -> Term -> Elab [Constraint]
checkWHNFConversion = undefined

checkSeqConversion :: Context -> [(Type, Term, Term)] -> Elab [Constraint]
checkSeqConversion = undefined

stripGuardedConstant :: Signature -> Signature
stripGuardedConstant = undefined
