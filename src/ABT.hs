module ABT where
import Data.Set ( empty, singleton, unions, Set )

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
variables = ('`' : last variables) : ["x"]

fresh :: (ABTCompatible a) => [ABT a] -> VarName
fresh l = head $ filter (`elem` unions (map freeVariables l)) variables
