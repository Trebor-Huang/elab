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
         | otherwise = error $ "Failed!\n\n" ++ show m ++ "\n=====is not equal to=====\n" ++ show n

-- abstract and instantiate
test1 = test (abstract "x" (Node (LamTest (Bind (FVar "x"))))) (Node (LamTest (Bind (BVar 1))))
test2 = test (instantiate t m) res
  where
      t = Node (AppTest (FVar "x") (Node (LamTest (Bind (BVar 0)))))
      m = Node (LamTest (Bind (Node (AppTest (BVar 1) (BVar 0)))))
      res = Node (LamTest (Bind (Node (AppTest (Node (AppTest (FVar "x") (Node (LamTest (Bind (BVar 0)))))) (BVar 0)))))

-- Test 3 to 5 follows the linked paper.
infixr ->:
(->:) x y = Node (Fun x (Bind y) True)
infixr ->?
(->?) x y = Node (Fun x (Bind y) False)

sig1 = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareEq "id" (Node Set ->: ( BVar 0 ->: BVar 1)) (Node (Lam (Bind (Node (Lam (Bind (BVar 0))))))),
    DeclareType "alpha" (Node Set)
    ]

elab1 :: Elab Term
elab1 = checkTerm [] (Node (UApp (Node (UApp (Node (UConst "id")) (Node Unknown) True)) (Node (UConst "0")) True)) (Node (Const "alpha"))

res1 = (Right (Node (App (Node (App (Node (Const "id")) (Node (Const "c")))) (Node (Const "0")))),
  [
    DeclareEq "c" (Node Set) (Node (Const "Nat")),
    DeclareEq "alpha" (Node Set) (Node (Const "Nat"))
  ] ++ tail sig1) -- alpha is assigned

test3 = test (runElab elab1 sig1) res1

sig2 = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareType "suc" (Node (Const "Nat") ->: Node (Const "Nat")),
    DeclareType "caseNat" (
          ({-P-} Node (Const "Nat") ->: Node Set)
      ->: Node (App (BVar 0 {-P-}) (Node (Const "0")))
      ->: (Node (Const "Nat") {-n'-} ->: Node (App (BVar 2 {-P-}) (Node (App (Node (Const "suc")) (BVar 0 {-n'-})))))
      ->: {-n-} Node (Const "Nat")
      ->: Node (App (BVar 3 {-P-}) (BVar 0 {-n-}))
      )
    ]

elab2 = checkTerm [] (Node (UApp
  (Node (UApp
    (Node (UApp
      (Node (UConst "caseNat"))
      (Node Unknown) True))
    (Node (UConst "0")) True))
  (Node (ULam (Bind (BVar 0)) True)) True))
  (Node (Const "Nat") ->: Node (Const "Nat"))

res2 = (Right (Node (Const "```c")),
  [
    DeclareConstraint "```c" (Node (Const "Nat") ->: Node (Const "Nat")) (Node (App (Node (App (Node (App (Node (Const "caseNat")) (Node (Const "c")))) (Node (Const "`c")))) (Node (Lam (Bind (Node (App (Node (Const "``c")) (BVar 0)))))))) [CTrm [("x",Node (Const "Nat"))] (Node Set) (Node (Const "Nat")) (Node (App (Node (Const "c")) (FVar "x")))],
    DeclareConstraint "``c" (Node (Const "Nat") ->: Node (App (Node (Const "c")) (Node (App (Node (Const "suc")) (BVar 0))))) (Node (Lam (Bind (BVar 0)))) [CTrm [("x",Node (Const "Nat"))] (Node Set) (Node (App (Node (Const "c")) (Node (App (Node (Const "suc")) (FVar "x"))))) (Node (Const "Nat"))],
    DeclareConstraint "`c" (Node (App (Node (Const "c")) (Node (Const "0")))) (Node (Const "0")) [CTrm [] (Node Set) (Node (App (Node (Const "c")) (Node (Const "0")))) (Node (Const "Nat"))],
    DeclareType "c" (Node (Const "Nat") ->: Node Set)
  ] ++ sig2)

test4 = test (runElab elab2 sig2) res2

sig3 = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareEq "coerce" -- \F x -> x  ::  (F : Nat -> Set) -> F 0 -> F 0
      ((Node (Const "Nat") ->: Node Set)
          ->: (Node (App (BVar 0) (Node (Const "0")))
          ->: Node (App (BVar 1) (Node (Const "0")))))
      (Node (Lam (Bind (Node (Lam (Bind (BVar 0)))))))
  ]

elab3 = checkTerm []
  (Node (ULam
    (Node (UApp
      (BVar 0)
      (Node (UApp
        (Node (UApp
          (Node $ UConst "coerce")
          (Node Unknown) True))
        (BVar 0) True)) True)) True))
  ((Node (Const "Nat") ->: Node (Const "Nat"))
    ->: Node (Const "Nat"))

test5 = test (runElab elab3 sig3)
  (Left (TypeInferenceFailed
    (Node (ULam
      (Node (UApp
        (BVar 0)
        (Node (UApp
          (Node (UApp
            (Node (UConst "coerce"))
            (Node Unknown) True))
          (BVar 0) True)) True)) True))), sig3)

typeFlip = Node Set ->? (BVar 0 ->: BVar 1 ->: BVar 2) ->: BVar 1 ->: BVar 2 ->: BVar 3

elaboratedFlip = Node (Lam (Bind
  (Node (Lam (Bind
    (Node (Lam (Bind
      (Node (Lam (Bind
        (Node (App
          (Node (App
            (BVar 2)
            (BVar 0)))
          (BVar 1))))))))))))))

termFlip = Node (ULam (Bind -- A
  (Node (ULam (Bind -- F
    (Node (ULam (Bind -- a
      (Node (ULam (Bind -- b
        (Node (UApp
          (Node (UApp
            (BVar 2)
            (BVar 0) True))
          (BVar 1) True)))
          True)))
          True)))
          True)))
          False)

termFlip' = Node (ULam (Bind -- F
    (Node (ULam (Bind -- a
      (Node (ULam (Bind -- b
        (Node (UApp
          (Node (UApp
            (BVar 2)
            (BVar 0) True))
          (BVar 1) True)))
          True)))
          True)))
          True) -- \A is implicit

termFlip'' = Node (ULam (Bind -- F
    (Node (ULam (Bind -- a
      (Node (ULam (Bind -- b
        (Node (UApp
          (Node (UApp
            (Node (UApp
              (Node (UConst "flip"))
              (BVar 2) True))
            (BVar 1) True))
          (BVar 0) True)))
          True)))
          True)))
          True)

elaboratedFlip'' = Node (Lam (Bind (Node (Lam (Bind (Node (Lam (Bind (Node (Lam (Bind (Node (App (Node (App (Node (App (Node (App (Node (Const "flip")) (Node (App (Node (App (Node (App (Node (App (Node (Const "c")) (BVar 3))) (BVar 2))) (BVar 1))) (BVar 0))))) (BVar 2))) (BVar 1))) (BVar 0))))))))))))))

elab4 = checkTerm [] termFlip typeFlip
elab5 = checkTerm [] termFlip' typeFlip
elab6 = checkTerm [] termFlip'' typeFlip

test6 = test (runElab elab4 []) (Right elaboratedFlip, [])

test7 = test (runElab elab5 []) (Right elaboratedFlip, [])

test8 = test (runElab elab6 [DeclareEq "flip" typeFlip elaboratedFlip]) (Right elaboratedFlip'',
  [
    DeclareEq "c" (Node Set  -- (A : Set) -> (A -> A -> A) -> A -> A -> Set
      ->: (BVar 0 ->: BVar 1 ->: BVar 2)
      ->: BVar 1
      ->: BVar 2
      ->: Node Set)

      (Node (Lam (Bind
        (Node (Lam (Bind
          (Node (Lam (Bind
            (Node (Lam (Bind
              (BVar 3))))))))))))), -- \ A f b c -> A
    DeclareEq "flip" typeFlip elaboratedFlip])

tests :: [String]
tests = [test1, test2, test3, test4, test5, test6, test7, test8]

main :: IO ()
main = putStrLn (intercalate "\n" tests)
