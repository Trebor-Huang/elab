module ABT where
import Data.Set ( empty, singleton, unions, union, fromList, Set )

type VarName = String

data ABT a = Node a | FVar VarName | BVar Int | Bind (ABT a) deriving (Eq, Show, Ord)
type Scope = ABT

class (ABTCompatible a) where
  collect :: (Ord b) => (ABT a -> b) -> a -> Set b
  fallthrough :: (ABT a -> ABT a) -> a -> a

everywhere :: (ABTCompatible a) =>
  (VarName -> ABT a) -> -- Free variables
  (Int -> ABT a) -> -- Bound variables
  (ABT a -> ABT a) -> -- Binders
  ABT a ->
  ABT a
everywhere fv bv bn (Node n) = Node (fallthrough (everywhere fv bv bn) n)
everywhere fv bv bn (FVar s) = fv s
everywhere fv bv bn (BVar i) = bv i
everywhere fv bv bn (Bind n) = bn n

abstract :: (ABTCompatible a) => VarName -> ABT a -> Scope a
abstract vn = name 0 vn
  where
    name k vn =
      everywhere
        (check k)
        BVar
        (Bind . name (k + 1) vn)
    check k vn'
      | vn == vn' = BVar k
      | otherwise = FVar vn'

instantiate :: (ABTCompatible a) => ABT a -> Scope a -> ABT a
instantiate t = replace 0 t
  where
    replace k t =
      everywhere
        FVar
        (check k)
        (Bind . replace (k + 1) t)
    check k b
      | k == b = t
      | otherwise = BVar b

substitute :: (ABTCompatible a) => ABT a -> VarName -> ABT a -> ABT a
substitute m x n = instantiate m $ abstract x n

freeVariables :: (ABTCompatible a) => ABT a -> Set VarName
freeVariables (Node a) = unions (collect freeVariables a)
freeVariables (Bind a) = freeVariables a
freeVariables (FVar x) = singleton x
freeVariables (BVar i) = empty

variables :: [VarName]
variables = "x" : map ('`' : ) variables

-- generate fresh names
-- the first argument lets you supply a list of terms
-- so that you are saved the trouble of extracting free variables out of them
-- the second argument is for (map fst ctx), extracting variables from contexts
-- todo actually I realized that the first argument is just useless
-- todo we might use the state monad to get a gensym stuff instead
fresh :: [VarName] -> VarName
fresh l  = head $ filter (`notElem` fromList l) variables

-- if that doesn't do, use this one, which is more flexible
fresh' :: (Foldable t) => t VarName -> VarName
fresh' s = head $ filter (`notElem` s) variables
