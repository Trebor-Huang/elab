module TT where
import ABT
import Control.Monad.State ( StateT, gets, MonadState(get, put), runStateT )
import Control.Monad.Except ( MonadError(throwError, catchError), ExceptT, runExceptT )
import Control.Monad.Identity ( Identity, runIdentity )
import Data.Set (Set, union, unions, singleton, empty, toList, fromList)
import Data.List (zip4)
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
funcContext ((x, m):xs) t = funcContext xs (Node (m :-> Bind (abstract x t)))

substContext :: Context -> [Term] -> Term -> Term
substContext [] [] = id
substContext ((x, m):xs) (s:ss) = substContext xs ss . substitute s x
substContext _ _ = error "Length mismatch"

appContext :: Term -> Context -> Term
appContext t [] = t
appContext t ((x, _):xs) = Node (App (appContext t xs) (FVar x))

lamContext :: Context -> Term -> Term
lamContext [] t = t
lamContext ((x, m):xs) t = lamContext xs $ Node $ Lam $ abstract x t

funcTelescope :: Telescope -> Type -> Type
funcTelescope [] t = t
funcTelescope ((x, m):xs) t = Node (m :-> Bind (abstract x (funcTelescope xs t)))

appTelescope :: Term -> Telescope -> Term
appTelescope t [] = t
appTelescope t ((x, _): xs) = appTelescope (Node $ App t $ FVar x) xs

lamTelescope :: Telescope -> Term -> Term
lamTelescope [] t = t
lamTelescope ((x, m):xs) t = Node $ Lam $ abstract x $ lamTelescope xs t

substTelescope :: Telescope -> [Term] -> Term ->  Term
substTelescope [] [] = id
substTelescope ((x,a):xs) (s:ss) =  substitute s x . substTelescope xs ss
substTelescope _ _ = error "Length mismatch"

contextDistinct :: Context -> Bool
contextDistinct = hasDuplicate . map fst

data SignatureSnippet =
      DeclareType ConstName Type
    | DeclareEq ConstName Type Term
    | DeclareConstraint ConstName Type Term [Constraint] -- New
    deriving (Eq, Show)
type Signature = [SignatureSnippet]  -- ! Snoc list
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

data Constraint =
      CTyp Context Type Type
    | CTrm Context Type Term Term
    | CTms Context [(VarName, Term, Term, Type)]
    deriving (Eq, Show)

data UserExpr' =
      ULam UserExpr
    | UApp UserExpr UserExpr -- ! No beta allowed, prevent at parsing
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

data WHNF = VariableHead {  -- arguments in natural order
    variableHead :: VarName,
    arguments :: [Term]
} | ConstHead {
    constHead :: ConstName,
    arguments :: [Term]
} deriving (Show, Eq)

forgetWHNF :: WHNF -> Term
forgetWHNF w = case w of
    (VariableHead v xs) -> helper (FVar v) xs
    (ConstHead c xs) -> helper (Node $ Const c) xs
    where
        helper tm [] = tm
        helper tm (x:xs) = helper (Node (App tm x)) xs

data TypeCheckingFailures =
      NonUniqueConst ConstName
    | ConstNotFound ConstName
    | VariableNotFound VarName
    | ConstAlreadyAssigned ConstName
    | ScopeCheckFailed ConstName Term
    | TypeInferenceFailed
    | CannotConvertToFunction
    | WHNFNotConvertible
    deriving (Show, Eq)

type Elab a = ExceptT TypeCheckingFailures (StateT Signature Identity) a
-- The main monad where we work.
-- The IO inside is for logging. So when the debug is finished it shouldn't be there.
-- Just replace it with Identity

runElab :: Elab a -- ^ The elaboration process
  -> Signature -- ^ The initial signature to work with
  -> (Either TypeCheckingFailures a, Signature)
runElab e s = runIdentity $ runStateT (runExceptT e) s

addMeta :: ConstName -> Type -> Elab ()
addMeta c t = do
    s <- get
    if c `elem` map getName s then
        throwError $ NonUniqueConst c
    else
        put $ DeclareType c t : s

addAssignment :: ConstName -> Term -> Elab ()
addAssignment c t = do
    s <- get
    let (p, q) = break ((c ==) . getName) s
    if null q then
        throwError $ ConstNotFound c
    else case head q of
        DeclareType c' t' -> put (p ++ DeclareEq c t' t : tail q)
        _ -> throwError $ ConstAlreadyAssigned c

addConst :: ConstName -> Type -> Term -> [Constraint] -> Elab ()
addConst c ty tm cs = do
    s <- get
    if c `elem` map getName s then
        throwError $ NonUniqueConst c
    else
        put $ DeclareConstraint c ty tm cs : s

inScope :: ConstName -> Term -> Elab ()
inScope c t = do
    s <- get
    case break ((c ==) . getName) s of
        (p, DeclareType _ t' : q) ->
            if all (`elem` map getName q) (toList $ allConstants t) then
                return ()
            else
                throwError $ ScopeCheckFailed c t
        (p, _ : q) -> throwError $ ConstAlreadyAssigned c
        (p, _) -> throwError $ ConstNotFound c

lookUpConstant :: ConstName -> Elab Type
lookUpConstant c = do
    s <- gets (filter ((==c).getName))
    if null s then
        throwError $ ConstNotFound c
    else
        return $ getType $ head s

checkType :: Context -> UserExpr -> Elab Type
checkType ctx (Node USet) = return (Node Set)
checkType ctx e@(Node (UFun e1 (Bind e2))) = do
    t1 <- checkType ctx e1
    let x = fresh [e1, e2] (map fst ctx)
    t2 <- checkType ((x, t1) : ctx) (instantiate (FVar x) e2)
    return $ Node (t1 :-> Bind (abstract x t2))
    `catchError` const (checkTerm ctx e (Node Set))
checkType ctx e = checkTerm ctx e (Node Set)

checkTerm :: Context -> UserExpr -> Type -> Elab Term
checkTerm ctx e0@(Node (ULam (Bind e))) t0@(Node (a :-> (Bind b))) = do
    let x = fresh' (unions [freeVariables e, freeVariables a, freeVariables b])
    Node . Lam . Bind . abstract x <$>
      checkTerm ((x, a) : ctx) (instantiate (FVar x) e) (instantiate (FVar x) b)
    `catchError` const (_checkTermFallBack ctx e0 t0)
checkTerm ctx (Node Unknown) t = do
    c <- gets freshConstant
    addMeta c (funcContext ctx t)
    return (appContext (Node (Const c)) ctx)
checkTerm ctx e t = _checkTermFallBack ctx e t

_checkTermFallBack ctx e t = do
    (t', s) <- inferType ctx e
    constraints <- checkTypeConversion ctx t t'
    if null constraints then
        return s
    else do
        p <- gets freshConstant
        addConst p (funcContext ctx t) (lamContext ctx s) constraints
        return (appContext (Node (Const p)) ctx)

inferType :: Context -> UserExpr -> Elab (Type, Term)
inferType ctx (FVar x) = do
    case lookup x ctx of
        Just t -> return (t, FVar x)
        _ -> throwError $ VariableNotFound x
inferType ctx (Node (UConst c)) = do
    s <- lookUpConstant c
    return (s, Node (Const c))
inferType ctx (Node (UApp m n)) = do
    x <- inferType ctx m
    case x of
        (Node (t1 :-> (Bind t2)), s) -> do
            t <- checkTerm ctx n t1
            return (instantiate t t2, Node (App s t))
        (_, s) -> throwError CannotConvertToFunction
inferType ctx _ = throwError TypeInferenceFailed

checkTypeConversion :: Context -> Type -> Type -> Elab [Constraint]
checkTypeConversion ctx (Node Set) (Node Set) = return []
checkTypeConversion ctx (Node (a1 :-> (Bind b1))) (Node (a2 :-> (Bind b2)))
    = do  -- TODO in the future needs backtracking
        constraints <- checkTypeConversion ctx a1 a2
        let x = fresh [a1, a2, b1, b2] (map fst ctx)
        if null constraints then do
            checkTypeConversion ((x, a1):ctx) (instantiate (FVar x) b1) (instantiate (FVar x) b2)
        else do
            p <- gets freshConstant
            addConst p
                (funcContext ctx $ Node (a1 :-> Bind a2))
                (lamContext ctx $ Node (Lam (Bind (BVar 0))))
                constraints
            constraints' <- checkTypeConversion ((x, a1):ctx)
                (instantiate (Node (App (appContext (Node (Const p)) ctx) (FVar x))) b1)
                (instantiate (Node (App (appContext (Node (Const p)) ctx) (FVar x))) b2)
            return $ constraints ++ constraints'
checkTypeConversion ctx t1 t2 = checkTermConversion ctx (Node Set) t1 t2

checkTermConversion :: Context -> Type -> Term -> Term -> Elab [Constraint]
checkTermConversion ctx (Node (a :-> (Bind b))) s t = do
    let x = fresh [a,b,s,t] (map fst ctx)
    checkTermConversion ((x, a):ctx)
        (instantiate (FVar x) b)
        (Node (App s (FVar x)))
        (Node (App t (FVar x)))
checkTermConversion ctx a s t = do
    s' <- computeWHNF s
    t' <- computeWHNF t
    checkWHNFConversion ctx a s' t'

checkWHNFConversion :: Context -> Type -> WHNF -> WHNF -> Elab [Constraint]
checkWHNFConversion ctx a' (VariableHead h ss) (VariableHead h' ts)
    | h == h' && ss == ts = return []
    | h == h' && length ss == length ts = do
        case lookup h ctx of
            Just t -> do
                (delta, a) <- seperateArguments ctx t (length ss)
                constraints <- checkSeqConversion ctx $ zip4 (map fst ctx) (map snd ctx) ss ts
                if a' == substTelescope delta ss a
                    then return constraints
                    else error "Type mismatch"  -- ! code unreachable, will remove
            _ -> throwError $ VariableNotFound h
    | otherwise =
        throwError WHNFNotConvertible
            where
                seperateArguments :: Context -> Type -> Int -> Elab (Telescope, Type)
                seperateArguments ctx a 0 = return ([], a)
                seperateArguments ctx (Node (a :-> (Bind b))) n = do
                    let x = fresh ([]::[Term]) (map fst ctx)
                    (delta, t) <- seperateArguments ((x,a):ctx) (instantiate (FVar x) b) (n-1)
                    return ((x,a):delta, t)
                seperateArguments _ _ _ = throwError WHNFNotConvertible
checkWHNFConversion ctx a f@(ConstHead c ss) t | f == t = return []
    -- this is the important part.
    -- it actually does all the unification work.
    -- (currently it is very rudimentary)
                                               | otherwise =
    if distinctVariables ss then do
        s' <- computeNF (forgetWHNF t)
        if all ((`elem` ss).FVar) (freeVariables s') then do
            let expr = lamTelescope [(x, undefined) | FVar x <- ss] s'
            inScope c expr
            addAssignment c expr
            return []
            `catchError` const 
                (return [CTrm ctx a (forgetWHNF f) (forgetWHNF t)])
        else
            return [CTrm ctx a (forgetWHNF f) (forgetWHNF t)]
    else
        return [CTrm ctx a (forgetWHNF f) (forgetWHNF t)]  -- Aww, look at these three.. Got to be better ways
    where
        distinctVariables :: [Term] -> Bool
        distinctVariables [] = True
        distinctVariables ((FVar x) : xs) = distinctVariables xs && FVar x `notElem` xs
        distinctVariables _ = False
checkWHNFConversion ctx a s t = throwError WHNFNotConvertible

computeNF :: Term -> Elab Term
computeNF (Node (Const c)) = do
    s <- gets (filter ((==c).getName))
    case s of
        DeclareConstraint _ ty tm g : _ | null g -> return tm
                                        | otherwise -> return $ Node $ Const c
        DeclareEq _ ty tm : _ -> return tm
        DeclareType _ ty : _ -> return $ Node $ Const c
        [] -> throwError $ ConstNotFound c
computeNF (Node (App (Node (Lam (Bind m))) n)) = computeNF (instantiate n m)
computeNF (Node (App m n)) = Node <$> (App <$> computeNF m <*> computeNF n)
computeNF (Node (Lam (Bind m))) = do
    let x = fresh [m] []
    Node . Lam . Bind . abstract x <$> computeNF (instantiate (FVar x) m)
computeNF (FVar x) = return (FVar x)
computeNF _ = error "Unexpected Syntax!"

computeWHNF :: Term -> Elab WHNF
computeWHNF (Node (Const c)) = do
    s <- gets (filter ((==c).getName))
    case s of
        DeclareConstraint _ ty tm g : _ | null g -> computeWHNF tm
                                        | otherwise -> return $ ConstHead c []
        DeclareEq _ ty tm : _ -> computeWHNF tm
        DeclareType _ ty : _ -> return $ ConstHead c []
        [] -> throwError $ ConstNotFound c
computeWHNF (Node (App (Node (Lam (Bind m))) n)) = computeWHNF (instantiate n m)
computeWHNF (Node (App m n)) = do
    m' <- computeWHNF m
    return m'{arguments = arguments m' ++ [n]}  -- O(n^2). Might do the reversal at the end?
computeWHNF (Node (Lam _)) = error "Lambdas should have been stripped already"
computeWHNF (FVar x) = return $ VariableHead x []
computeWHNF _ = error "Unexpected Syntax!"

checkSeqConversion :: Context -> [(VarName, Type, Term, Term)] -> Elab [Constraint]
checkSeqConversion ctx [] = return []
checkSeqConversion ctx [(x, ty, t1, t2)] = checkTermConversion ctx ty t1 t2
checkSeqConversion ctx eqs'@((x, ty, t1, t2):eqs) = do
    c0 <- checkTermConversion ctx ty t1 t2
    if null c0 then
        checkSeqConversion ctx [(x', substitute t1 x ty', t1', t2') | (x', ty', t1', t2') <- eqs]
    else if any ((x `elem`). freeVariables . snd4) eqs then
        return [CTms ctx eqs']
    else do
        c1 <- checkSeqConversion ctx eqs
        return (c0 ++ c1)
        where snd4 (a,b,c,d) = b

stripGuardedConstant :: Signature -> Signature
stripGuardedConstant = map strip
    where
        strip :: SignatureSnippet -> SignatureSnippet
        strip (DeclareConstraint c t tm g) | null g = DeclareEq c t tm
                                           | otherwise = DeclareType c t
        strip s = s
