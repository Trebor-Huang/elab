import ABT
import TT
import Data.List (intercalate)
import Data.Set ( fromList, singleton )

data NodeType = LamTest (ABT NodeType) | AppTest (ABT NodeType) (ABT NodeType) deriving (Eq, Show)
instance (ABTCompatible NodeType) where
  fallthrough f (LamTest n) = LamTest (f n)
  fallthrough f (AppTest m n) = AppTest (f m) (f n)

  collect f (LamTest n) = singleton $ f n
  collect f (AppTest m n) = fromList [f m, f n]

test :: (Eq a, Show a) => a -> a -> String
test m n | m == n = "Passed."
         | otherwise = "Failed!\n" ++ show m ++ " is not equal to " ++ show n

-- abstract and instantiate
test1 = test (abstract "x" (Node (LamTest (Bind (FVar "x"))))) (Node (LamTest (Bind (BVar 1))))
test2 = test (instantiate t m) res
  where
      t = Node (AppTest (FVar "x") (Node (LamTest (Bind (BVar 0)))))
      m = Node (LamTest (Bind (Node (AppTest (BVar 1) (BVar 0)))))
      res = Node (LamTest (Bind (Node (AppTest (Node (AppTest (FVar "x") (Node (LamTest (Bind (BVar 0)))))) (BVar 0)))))

-- Test 3 to 5 follows the linked paper.
sig1 = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareEq "id" (Node (Node Set :-> Bind (Node (BVar 0 :-> Bind (BVar 1))))) (Node (Lam (Bind (Node (Lam (Bind (BVar 0))))))),
    DeclareType "alpha" (Node Set)
    ]

elab1 :: Elab Term
elab1 = checkTerm [] (Node (UApp (Node (UApp (Node (UConst "id")) (Node Unknown))) (Node (UConst "0")))) (Node (Const "alpha"))

test3 = show $ runElab elab1 sig1

sig2 = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareType "suc" (Node (Node (Const "Nat") :-> Bind (Node (Const "Nat")))),
    DeclareType "caseNat" _ -- Too long I can't write it by hand
    ]

test4 = _

test5 = _ -- This should fail

{-
The following is an example mentioned by ice1000

test : (a : _) (B : Set) (b : B) -> a ≡ b
test a B b = refl

Where

_≡_ : {A : Set} -> A -> A -> Set
refl : {A : Set}(a : A) -> a ≡ a

This will be done after we have implicit binders

-}

tests :: [String]
tests = [test1, test2, test3, test4, test5]

main :: IO ()
main = putStrLn (intercalate "\n" tests)
