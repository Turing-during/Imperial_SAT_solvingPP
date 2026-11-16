module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp key = fromJust . lookup key

-- 3 marks
vars :: Formula -> [Id]
vars = sort . nub . varsy
    where
        varsy :: Formula -> [Id]
        varsy (Var x) = [x]
        varsy (Not f) =  vars f
        varsy (And f1 f2) = vars f1 ++ vars f2
        varsy (Or f1 f2) = vars f1 ++ vars f2

-- 1 mark
idMap :: Formula -> IdMap
idMap f = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (And f1 f2)) = Or (toNNF $ Not f1) (toNNF $ Not f2)
toNNF (Not (Or f1 f2)) = And (toNNF $ Not f1) (toNNF $ Not f2)
toNNF (Not (Not f)) = toNNF f
toNNF (And f1 f2) = And (toNNF f1) (toNNF f2)
toNNF (Or f1 f2) = Or (toNNF f1) (toNNF f2)
toNNF f = f


-- 3 marks
toCNF :: Formula -> CNF
toCNF f = case (toNNF f) of
    Or f1 f2 -> distribute (toCNF f1) (toCNF f2)
    And f1 f2 -> And (toCNF f1) (toCNF f2)
    _ -> f

-- 4 marks
flatten :: CNF -> CNFRep
flatten 
  = undefined

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits 
  = undefined

-- 4 marks
dp :: CNFRep -> [[Int]]
dp 
  = undefined

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined


