module Main where

import TT
import ABT

sig = reverse [
    DeclareType "Nat" (Node Set),
    DeclareType "0" (Node (Const "Nat")),
    DeclareEq "id" (Node (Node Set :-> Bind (Node (BVar 0 :-> Bind (BVar 1))))) (Node (Lam (Bind (Node (Lam (Bind (BVar 0))))))),
    DeclareType "alpha" (Node Set)
    ]

elab1 :: Elab Term
elab1 = checkTerm [] (Node (UApp (Node (UApp (Node (UConst "id")) (Node Unknown))) (Node (UConst "0")))) (Node (Const "alpha"))

res1 = runElab elab1 sig

main :: IO ()
main = do
    r <- res1
    print r
