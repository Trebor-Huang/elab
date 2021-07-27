import ABT
import Data.List (intercalate)
import Data.Set ( fromList, singleton )

data NodeType = Lam (ABT NodeType) | App (ABT NodeType) (ABT NodeType) deriving (Eq, Show)
instance (ABTCompatible NodeType) where
  fallthrough f (Lam n) = Lam (f n)
  fallthrough f (App m n) = App (f m) (f n)

  collect f (Lam n) = singleton $ f n
  collect f (App m n) = fromList [f m, f n]

test :: (Eq a, Show a) => a -> a -> String
test m n | m == n = "Passed."
         | otherwise = "Failed!\n" ++ show m ++ " is not equal to " ++ show n

-- abstract and instantiate
test1 = test (abstract "x" (Node (Lam (Bind (FVar "x"))))) (Node (Lam (Bind (BVar 1))))
test2 = test (instantiate t m) res
  where
      t = Node (App (FVar "x") (Node (Lam (Bind (BVar 0)))))
      m = Node (Lam (Bind (Node (App (BVar 1) (BVar 0)))))
      res = Node (Lam (Bind (Node (App (Node (App (FVar "x") (Node (Lam (Bind (BVar 0)))))) (BVar 0)))))

tests :: [String]
tests = [test1, test2]

main :: IO ()
main = putStrLn (intercalate "\n" tests)
